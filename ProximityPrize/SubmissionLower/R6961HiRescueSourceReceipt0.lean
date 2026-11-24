import ProximityPrize.SubmissionLower.R6961HiRescueSourceSchedule

set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 18000

namespace Lower6961.Hi.RescueSource
open P1_7 (Bank debit)
open P1_7_1_3 (blockEstimate block_append momentEstimate)
open Lower6960.HelperSource (WidthGuard)
open Lower6960.RescueSource (fastLayer fastPhase)

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

private theorem mkP (r : Fin 4) (s : Fin 17) (h a b c d e n z : ℕ) (cs : List (ℕ × ℕ))
    (hsz : (bank r s).shape.J / b + 1 = n)
    (hn : (cs.map Prod.fst).sum = n) (hz : (cs.map Prod.snd).sum = z)
    (hc : blk (fastLayer (bank r s).shape 179818 h a b c d e) 0 cs) :
    fastPhase (bank r s).shape 179818 h a b c d e = z :=
  phase_of_block hsz (by rw [← hn, ← hz]; exact blk_sum hc)


private def mblk (B J : ℕ) : ℕ → List (ℕ × ℕ) → Prop
  | _, [] => True
  | s, (n, v) :: rest => blockEstimate B J s n = v ∧ mblk B J (s + n) rest

private theorem mblk_sum {B J s : ℕ} {cs : List (ℕ × ℕ)} (h : mblk B J s cs) :
    blockEstimate B J s (cs.map Prod.fst).sum = (cs.map Prod.snd).sum := by
  induction cs generalizing s with
  | nil => rfl
  | cons cv rest ih =>
    rcases cv with ⟨n, v⟩
    rcases h with ⟨h1, h2⟩
    exact block_append h1 (ih h2) rfl rfl rfl

private theorem mkM (B J z : ℕ) (cs : List (ℕ × ℕ))
    (hn : (cs.map Prod.fst).sum = B + J) (hz : (cs.map Prod.snd).sum = z)
    (hc : mblk B J J cs) : momentEstimate B J = z := by
  unfold momentEstimate; rw [← hn, ← hz]; exact mblk_sum hc

theorem moment_907_192 : momentEstimate 907 192 = 18389221088 := mkM 907 192 18389221088 [(128,290411680),(128,1705328752),(128,3224576064),(128,3967672384),(128,3901268032),(128,3032779128),(128,1688215192),(128,546427967),(75,32541889)] rfl rfl (by dsimp only [mblk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

theorem moment_1257_266 : momentEstimate 1257 266 = 67643823442 := mkM 1257 266 67643823442 [(128,415627680),(128,2599438752),(128,5961006051),(128,8681797632),(128,10282874880),(128,10764072960),(128,10125391872),(128,8369214195),(128,5801507064),(128,3249804063),(128,1234496544),(115,158591749)] rfl rfl (by dsimp only [mblk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem receipt_0_0_2450_0 : fastPhase (bank 0 0).shape 179818 2450 0 1 0 1 0 = 1220402714529557300960562 := mkP 0 0 2450 0 1 0 1 0 267 1220402714529557300960562 [(128,918710943731356591296024),(128,299836059767659959603508),(11,1855711030540750061030)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem receipt_0_0_2450_1 : fastPhase (bank 0 0).shape 179818 2450 0 1 0 1 1 = 1210489455741924772921674 := mkP 0 0 2450 0 1 0 1 1 267 1210489455741924772921674 [(128,913310084692227647715016),(128,295634021439055509036454),(11,1545349610641616170204)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem receipt_0_0_2451_0 : fastPhase (bank 0 0).shape 179818 2451 0 1 0 1 0 = 1220412203571301342847756 := mkP 0 0 2451 0 1 0 1 0 267 1220412203571301342847756 [(128,918718669793641162077307),(128,299837815821365076007115),(11,1855717956295104763334)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem receipt_0_0_2451_1 : fastPhase (bank 0 0).shape 179818 2451 0 1 0 1 1 = 1210498885027456023386081 := mkP 0 0 2451 0 1 0 1 1 267 1210498885027456023386081 [(128,913317773090650306462564),(128,295635756536614076219675),(11,1545355400191640703842)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

theorem receipt_0_0 : Checked (bank 0 0) 0 0 1 := by
  refine checked_from_values (bank 0 0) 0 0 1
    (P3_7_1.checked (bank 0 0) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1257_266)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_0_0_2450_0 receipt_0_0_2450_1 receipt_0_0_2451_0 receipt_0_0_2451_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_1_0_2450_0 : fastPhase (bank 1 0).shape 179818 2450 0 1 0 2 0 = 1090790145679828707687291 := mkP 1 0 2450 0 1 0 2 0 267 1090790145679828707687291 [(128,822904110441391372151742),(128,266248919652518180752965),(11,1637115585919154782584)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem receipt_1_0_2450_1 : fastPhase (bank 1 0).shape 179818 2450 0 1 0 2 1 = 1081873942170965670521136 := mkP 1 0 2450 0 1 0 2 1 267 1081873942170965670521136 [(128,818008136567640612749388),(128,262502560694398703725419),(11,1363244908926354046329)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem receipt_1_0_2451_0 : fastPhase (bank 1 0).shape 179818 2451 0 1 0 2 0 = 1090798633598564208084237 := mkP 1 0 2451 0 1 0 2 0 267 1090798633598564208084237 [(128,822911032428761322314920),(128,266250479473933334515097),(11,1637121695869551254220)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem receipt_1_0_2451_1 : fastPhase (bank 1 0).shape 179818 2451 0 1 0 2 1 = 1081882376142772197353216 := mkP 1 0 2451 0 1 0 2 1 267 1081882376142772197353216 [(128,818015024318215709696874),(128,262504101808307679238106),(11,1363250016248808418236)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

theorem receipt_1_0 : Checked (bank 1 0) 0 0 2 := by
  refine checked_from_values (bank 1 0) 0 0 2
    (P3_7_1.checked (bank 1 0) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1257_266)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_1_0_2450_0 receipt_1_0_2450_1 receipt_1_0_2451_0 receipt_1_0_2451_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_2_0_2450_0 : fastPhase (bank 2 0).shape 179818 2450 0 1 0 7 0 = 561589278959555782952766 := mkP 2 0 2450 0 1 0 7 0 267 561589278959555782952766 [(128,430289916542177208347517),(128,130535983217606625876060),(11,763379199771948729189)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem receipt_2_0_2450_1 : fastPhase (bank 2 0).shape 179818 2450 0 1 0 7 1 = 556786374268461119712891 := mkP 2 0 2450 0 1 0 7 1 267 556786374268461119712891 [(128,427507515188186601600438),(128,128643433371542176760859),(11,635425708732341351594)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem receipt_2_0_2451_0 : fastPhase (bank 2 0).shape 179818 2451 0 1 0 7 0 = 561593673973946796847467 := mkP 2 0 2451 0 1 0 7 0 267 561593673973946796847467 [(128,430293542195043634888000),(128,130536749730008476665437),(11,763382048894685294030)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem receipt_2_0_2451_1 : fastPhase (bank 2 0).shape 179818 2451 0 1 0 7 1 = 556790739463176768263876 := mkP 2 0 2451 0 1 0 7 1 267 556790739463176768263876 [(128,427511121028958053825314),(128,128644190344842018464126),(11,635428089376695974436)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

theorem receipt_2_0 : Checked (bank 2 0) 0 0 7 := by
  refine checked_from_values (bank 2 0) 0 0 7
    (P3_7_1.checked (bank 2 0) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1257_266)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_2_0_2450_0 receipt_2_0_2450_1 receipt_2_0_2451_0 receipt_2_0_2451_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_3_0_2450_0 : fastPhase (bank 3 0).shape 179818 2450 0 1 1 1 0 = 80952740830554335664924 := mkP 3 0 2450 0 1 1 1 0 193 80952740830554335664924 [(128,73104593502600940133856),(65,7848147327953395531068)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem receipt_3_0_2450_1 : fastPhase (bank 3 0).shape 179818 2450 0 1 1 1 1 = 80032620921784589414928 := mkP 3 0 2450 0 1 1 1 1 193 80032620921784589414928 [(128,72432842793545650746720),(65,7599778128238938668208)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem receipt_3_0_2451_0 : fastPhase (bank 3 0).shape 179818 2451 0 1 1 1 0 = 80953289311820021047616 := mkP 3 0 2451 0 1 1 1 0 193 80953289311820021047616 [(128,73105118796221677845344),(65,7848170515598343202272)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem receipt_3_0_2451_1 : fastPhase (bank 3 0).shape 179818 2451 0 1 1 1 1 = 80033163554533910040080 := mkP 3 0 2451 0 1 1 1 1 193 80033163554533910040080 [(128,72433362919300093539680),(65,7599800635233816500400)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

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
