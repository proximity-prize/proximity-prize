import ProximityPrize.SubmissionLower.R6961HiRescueSourceSchedule

set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 18000

namespace Lower6961.Hi.RescueSource
open P1_7 (Bank debit)
open P1_7_1_3 (blockEstimate block_append momentEstimate)
open Lower6960.HelperSource (WidthGuard)
open Lower6960.RescueSource (fastLayer fastPhase)

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

private theorem p1 (r : Fin 4) (s : Fin 17) (h a b c d e n z : ℕ) (cs : List (ℕ × ℕ))
    (h1 : (bank r s).shape.J / b + 1 = n)
    (h2 : pchk (fastLayer (bank r s).shape 179808 h a b c d e) 0 cs = some (n, z)) :
    fastPhase (bank r s).shape 179808 h a b c d e = z :=
  phase_of_block h1 (pchk_sound h2)


private def mchk (B J : ℕ) : ℕ → List (ℕ × ℕ) → Option (ℕ × ℕ)
  | _, [] => some (0, 0)
  | s, (n, v) :: rest =>
      if blockEstimate B J s n == v then
        match mchk B J (s + n) rest with
        | some (tn, tv) => some (n + tn, v + tv)
        | none => none
      else none

private theorem mchk_sound {B J s tn tv : ℕ} {cs : List (ℕ × ℕ)}
    (h : mchk B J s cs = some (tn, tv)) : blockEstimate B J s tn = tv := by
  induction cs generalizing s tn tv with
  | nil =>
    simp only [mchk, Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩; rfl
  | cons cv rest ih =>
    rcases cv with ⟨n, v⟩
    unfold mchk at h
    split at h
    · rename_i heq
      cases hrest : mchk B J (s + n) rest with
      | none => simp [hrest] at h
      | some p =>
        rw [hrest] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        rcases h with ⟨rfl, rfl⟩
        exact block_append (Nat.eq_of_beq_eq_true heq) (ih hrest) rfl rfl rfl
    · simp at h

private theorem bs {B J s n1 v1 : ℕ} (n2 v2 n v : ℕ) (cs : List (ℕ × ℕ))
    (h1 : blockEstimate B J s n1 = v1) (h2 : mchk B J (s + n1) cs = some (n2, v2))
    (hn : n1 + n2 = n) (hv : v1 + v2 = v) : blockEstimate B J s n = v :=
  block_append h1 (mchk_sound h2) rfl hn hv

theorem moment_907_192 : momentEstimate 907 192 = 18389221088 := mchk_sound (by decide +kernel : mchk 907 192 192 [(128,290411680),(128,1705328752),(128,3224576064),(128,3967672384),(128,3901268032),(128,3032779128),(128,1688215192),(128,546427967),(75,32541889)] = some (1099,18389221088))

theorem moment_1257_266 : momentEstimate 1257 266 = 67643823442 := mchk_sound (by decide +kernel : mchk 1257 266 266 [(128,415627680),(128,2599438752),(128,5961006051),(128,8681797632),(128,10282874880),(128,10764072960),(128,10125391872),(128,8369214195),(128,5801507064),(128,3249804063),(128,1234496544),(115,158591749)] = some (1523,67643823442))


private theorem receipt_0_0_2450_0 : fastPhase (bank 0 0).shape 179808 2450 0 1 0 1 0 = 1610346975271053731625156 := p1 0 0 2450 0 1 0 1 0 267 1610346975271053731625156 [(128,1211957969529018937320229),(128,395936688363735880677139),(11,2452317378298913627788)] (by decide +kernel) (by decide +kernel)

private theorem receipt_0_0_2450_1 : fastPhase (bank 0 0).shape 179808 2450 0 1 0 1 1 = 1597275708889862149308823 := p1 0 0 2450 0 1 0 1 1 267 1597275708889862149308823 [(128,1204843104626916029857657),(128,390390416952610730765103),(11,2042187310335388686063)] (by decide +kernel) (by decide +kernel)

private theorem receipt_0_0_2451_0 : fastPhase (bank 0 0).shape 179808 2451 0 1 0 1 0 = 1610359495399432555489208 := p1 0 0 2451 0 1 0 1 0 267 1610359495399432555489208 [(128,1211968161764383906774192),(128,395939007103087862026094),(11,2452326531960786688922)] (by decide +kernel) (by decide +kernel)

private theorem receipt_0_0_2451_1 : fastPhase (bank 0 0).shape 179808 2451 0 1 0 1 1 = 1597288150260182868397403 := p1 0 0 2451 0 1 0 1 1 267 1597288150260182868397403 [(128,1204853247260651316424341),(128,390392708037192945960476),(11,2042194962338606012586)] (by decide +kernel) (by decide +kernel)

theorem receipt_0_0 : Checked (bank 0 0) 0 0 1 := by
  refine checked_from_values (bank 0 0) 0 0 1
    (P3_7_1.checked (bank 0 0) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1257_266)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_0_0_2450_0 receipt_0_0_2450_1 receipt_0_0_2451_0 receipt_0_0_2451_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_1_0_2450_0 : fastPhase (bank 1 0).shape 179808 2450 0 1 0 2 0 = 1440457054383480096812275 := p1 1 0 2450 0 1 0 2 0 267 1440457054383480096812275 [(128,1086125442153486901114578),(128,352162745260548062027798),(11,2168866969445133669899)] (by decide +kernel) (by decide +kernel)

private theorem receipt_1_0_2450_1 : fastPhase (bank 1 0).shape 179808 2450 0 1 0 2 1 = 1428700736355503983879795 := p1 1 0 2450 0 1 0 2 1 267 1428700736355503983879795 [(128,1079682281472048207706600),(128,347212392089768840985296),(11,1806062793686935187899)] (by decide +kernel) (by decide +kernel)

private theorem receipt_1_0_2451_0 : fastPhase (bank 1 0).shape 179808 2451 0 1 0 2 0 = 1440468261303507431458424 := p1 1 0 2451 0 1 0 2 0 267 1440468261303507431458424 [(128,1086134578044220423359426),(128,352164808194177422128938),(11,2168875065109585970060)] (by decide +kernel) (by decide +kernel)

private theorem receipt_1_0_2451_1 : fastPhase (bank 1 0).shape 179808 2451 0 1 0 2 1 = 1428711872209531330728832 := p1 1 0 2451 0 1 0 2 1 267 1428711872209531330728832 [(128,1079691372336051583505002),(128,347214430312521776507224),(11,1806069560957970716606)] (by decide +kernel) (by decide +kernel)

theorem receipt_1_0 : Checked (bank 1 0) 0 0 2 := by
  refine checked_from_values (bank 1 0) 0 0 2
    (P3_7_1.checked (bank 1 0) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1257_266)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_1_0_2450_0 receipt_1_0_2450_1 receipt_1_0_2451_0 receipt_1_0_2451_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_2_0_2450_0 : fastPhase (bank 2 0).shape 179808 2450 0 1 0 7 0 = 743845397510136321332989 := p1 2 0 2450 0 1 0 7 0 267 743845397510136321332989 [(128,568498819267677139079973),(128,174318415570119433359299),(11,1028162672339748893717)] (by decide +kernel) (by decide +kernel)

private theorem receipt_2_0_2450_1 : fastPhase (bank 2 0).shape 179808 2450 0 1 0 7 1 = 737530358088480036893974 := p1 2 0 2450 0 1 0 7 1 267 737530358088480036893974 [(128,564870825894448469841382),(128,171803646975999474765707),(11,855885218032092286885)] (by decide +kernel) (by decide +kernel)

private theorem receipt_2_0_2451_0 : fastPhase (bank 2 0).shape 179808 2451 0 1 0 7 0 = 743851213559123889438086 := p1 2 0 2451 0 1 0 7 0 267 743851213559123889438086 [(128,568503608299473945968940),(128,174319438749423387825048),(11,1028166510226555644098)] (by decide +kernel) (by decide +kernel)

private theorem receipt_2_0_2451_1 : fastPhase (bank 2 0).shape 179808 2451 0 1 0 7 1 = 737536135088657845861144 := p1 2 0 2451 0 1 0 7 1 267 737536135088657845861144 [(128,564875589163656256532452),(128,171804657499923816314380),(11,855888425077773014312)] (by decide +kernel) (by decide +kernel)

theorem receipt_2_0 : Checked (bank 2 0) 0 0 7 := by
  refine checked_from_values (bank 2 0) 0 0 7
    (P3_7_1.checked (bank 2 0) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1257_266)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_2_0_2450_0 receipt_2_0_2450_1 receipt_2_0_2451_0 receipt_2_0_2451_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_3_0_2450_0 : fastPhase (bank 3 0).shape 179808 2450 0 1 1 1 0 = 97505110045522057097930 := p1 3 0 2450 0 1 1 1 0 193 97505110045522057097930 [(128,88042204626581968829920),(65,9462905418940088268010)] (by decide +kernel) (by decide +kernel)

private theorem receipt_3_0_2450_1 : fastPhase (bank 3 0).shape 179808 2450 0 1 1 1 1 = 96397658622612428120784 := p1 3 0 2450 0 1 1 1 1 193 96397658622612428120784 [(128,87234148847032701011424),(65,9163509775579727109360)] (by decide +kernel) (by decide +kernel)

private theorem receipt_3_0_2451_0 : fastPhase (bank 3 0).shape 179808 2451 0 1 1 1 0 = 97505770653261822798072 := p1 3 0 2451 0 1 1 1 0 193 97505770653261822798072 [(128,88042837273683506765248),(65,9462933379578316032824)] (by decide +kernel) (by decide +kernel)

private theorem receipt_3_0_2451_1 : fastPhase (bank 3 0).shape 179808 2451 0 1 1 1 1 = 96398312192733975817760 := p1 3 0 2451 0 1 1 1 1 193 96398312192733975817760 [(128,87234775277015642390208),(65,9163536915718333427552)] (by decide +kernel) (by decide +kernel)

theorem receipt_3_0 : Checked (bank 3 0) 0 1 1 := by
  refine checked_from_values (bank 3 0) 0 1 1
    (P3_7_1.checked (bank 3 0) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_907_192)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_3_0_2450_0 receipt_3_0_2450_1 receipt_3_0_2451_0 receipt_3_0_2451_1 (by decide +kernel) (by decide +kernel)

def group0_stage (i : Fin 1) : Fin 17 :=
  ⟨0+i.val, by have := i.isLt; omega⟩

theorem group0_checked (rect : Fin 4) (i : Fin 1) :
    Checked (bank rect (group0_stage i)) (reserve (group0_stage i))
      (excess rect) (seed rect) := by
  fin_cases i
  · fin_cases rect
    · exact receipt_0_0
    · exact receipt_1_0
    · exact receipt_2_0
    · exact receipt_3_0

end Lower6961.Hi.RescueSource
