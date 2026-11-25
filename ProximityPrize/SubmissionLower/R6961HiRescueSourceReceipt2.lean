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

theorem moment_1696_356 : momentEstimate 1696 356 = 222371564601 := by
  unfold momentEstimate
  have h := mchk_sound (by decide +kernel : mchk 1696 356 356 [(128,572684320),(128,3684337696),(128,9136834131),(128,15370032384),(128,20341757184),(128,23816115456),(128,25793107200),(128,26272732416),(128,25254991104),(128,22739883264),(128,18755777396),(128,13945647249)] = some (1536,205683899800))
  have h := bs 516 16687664801 2052 222371564601 [(128,9230875643),(128,5110148823),(128,2022537952),(128,324080352),(4,22031)] h (by decide +kernel) (by decide) (by decide)
  exact h

theorem moment_1696_370 : momentEstimate 1696 370 = 229159736517 := by
  unfold momentEstimate
  have h := mchk_sound (by decide +kernel : mchk 1696 370 370 [(128,572684320),(128,3684337696),(128,9141056804),(128,15557757376),(128,20767001024),(128,24420157888),(128,26517227968),(128,27058211264),(128,26043107776),(128,23471917504),(128,19393615038),(128,14532053576)] = some (1536,211159128234))
  have h := bs 530 18000608283 2066 229159736517 [(128,9746328986),(128,5521630460),(128,2297261808),(128,434348784),(18,1038245)] h (by decide +kernel) (by decide) (by decide)
  exact h

theorem moment_1809_380 : momentEstimate 1809 380 = 287901786632 := by
  unfold momentEstimate
  have h := mchk_sound (by decide +kernel : mchk 1809 380 380 [(128,613111200),(128,3963594144),(128,9896705511),(128,17097207360),(128,23183453760),(128,27671670336),(128,30561857088),(128,31854014016),(128,31548141120),(128,29644238400),(128,26142305856),(128,21163152440)] = some (1536,253339451231))
  have h := bs 653 34562335401 2189 287901786632 [(128,15641164329),(128,10359919872),(128,5784462598),(128,2356385168),(128,419948944),(13,454490)] h (by decide +kernel) (by decide) (by decide)
  exact h

theorem moment_1809_395 : momentEstimate 1809 395 = 296724029248 := by
  unfold momentEstimate
  have h := mchk_sound (by decide +kernel : mchk 1809 395 395 [(128,613111200),(128,3963594144),(128,9896719776),(128,17253050925),(128,23627260800),(128,28340839296),(128,31393473408),(128,32785163136),(128,32515908480),(128,30585709440),(128,26994566016),(128,21919153025)] = some (1536,259888549646))
  have h := bs 668 36835479602 2204 296724029248 [(128,16340444489),(128,10971561561),(128,6272279892),(128,2685846592),(128,561511488),(28,3835580)] h (by decide +kernel) (by decide) (by decide)
  exact h

theorem moment_1817_380 : momentEstimate 1817 380 = 292013331876 := by
  unfold momentEstimate
  have h := mchk_sound (by decide +kernel : mchk 1817 380 380 [(128,615973280),(128,3983364512),(128,9950161303),(128,17198059584),(128,23334244416),(128,27872399424),(128,30812524608),(128,32154619968),(128,31898685504),(128,30044721216),(128,26592727104),(128,21638440059)] = some (1536,256095920978))
  have h := bs 661 35917410898 2197 292013331876 [(128,16076646528),(128,10730530099),(128,6072063646),(128,2541701328),(128,494759120),(21,1710177)] h (by decide +kernel) (by decide) (by decide)
  exact h

theorem moment_2285_480 : momentEstimate 2285 480 = 732176567216 := by
  unfold momentEstimate
  have h := mchk_sound (by decide +kernel : mchk 2285 480 480 [(128,783404960),(128,5139931040),(128,13077344160),(128,23780618088),(128,35332736192),(128,45144212672),(128,52938228928),(128,58714784960),(128,62473880768),(128,64215516352),(128,63939691712),(128,61646406848)] = some (1536,487186756680))
  have h := bs 1229 244989810536 2765 732176567216 [(128,57335661760),(128,51007456448),(128,42848244955),(128,34024165326),(128,25358865055),(128,17353338622),(128,10420160528),(128,5035269136),(128,1515991056),(77,90657650)] h (by decide +kernel) (by decide) (by decide)
  exact h

theorem moment_2285_498 : momentEstimate 2285 498 = 753510622290 := by
  unfold momentEstimate
  have h := mchk_sound (by decide +kernel : mchk 2285 498 498 [(128,783404960),(128,5139931040),(128,13077344160),(128,23789529417),(128,35672256512),(128,45924478976),(128,54083743744),(128,60150050816),(128,64123400192),(128,66003791872),(128,65791225856),(128,63485702144)] = some (1536,498024859689))
  have h := bs 1247 255485762601 2783 753510622290 [(128,59087220736),(128,52595798457),(128,44296056302),(128,35392420168),(128,26610909096),(128,18448620482),(128,11312632000),(128,5685571776),(128,1888735424),(95,167798160)] h (by decide +kernel) (by decide) (by decide)
  exact h


private theorem receipt_0_5_2450_0 : fastPhase (bank 0 5).shape 179808 2450 5 1 0 1 0 = 11591155742713559080496844 := p1 0 5 2450 5 1 0 1 0 357 11591155742713559080496844 [(128,7133290701898573094887584),(128,3645231962331047463445122),(101,812633078483938522164138)] (by decide +kernel) (by decide +kernel)

private theorem receipt_0_5_2450_1 : fastPhase (bank 0 5).shape 179808 2450 5 1 0 1 1 = 11520835372468822894189026 := p1 0 5 2450 5 1 0 1 1 357 11520835372468822894189026 [(128,7103906097982509586246560),(128,3620628363656818778599806),(101,796300910829494529342660)] (by decide +kernel) (by decide +kernel)

private theorem receipt_0_5_2451_0 : fastPhase (bank 0 5).shape 179808 2451 5 1 0 1 0 = 11591244068843567935333245 := p1 0 5 2451 5 1 0 1 0 357 11591244068843567935333245 [(128,7133351186826350400897088),(128,3645255938185133363152100),(101,812636943832084171284057)] (by decide +kernel) (by decide +kernel)

private theorem receipt_0_5_2451_1 : fastPhase (bank 0 5).shape 179808 2451 5 1 0 1 1 = 11520923282504252264415476 := p1 0 5 2451 5 1 0 1 1 357 11520923282504252264415476 [(128,7103966376113664376520448),(128,3620652199459848396192239),(101,796304706930739491702789)] (by decide +kernel) (by decide +kernel)

theorem receipt_0_5 : Checked (bank 0 5) 5 0 1 := by
  refine checked_from_values (bank 0 5) 5 0 1
    (P3_7_1.checked (bank 0 5) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1696_356)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_0_5_2450_0 receipt_0_5_2450_1 receipt_0_5_2451_0 receipt_0_5_2451_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_1_5_2450_0 : fastPhase (bank 1 5).shape 179808 2450 5 1 0 2 0 = 10389149221192294451996522 := p1 1 5 2450 5 1 0 2 0 357 10389149221192294451996522 [(128,6408938794617921624124224),(128,3257415302602344268884463),(101,722795123972028558987835)] (by decide +kernel) (by decide +kernel)

private theorem receipt_1_5_2450_1 : fastPhase (bank 1 5).shape 179808 2450 5 1 0 2 1 = 10325808760988809762038460 := p1 1 5 2450 5 1 0 2 1 357 10325808760988809762038460 [(128,6382266128508779515053120),(128,3235295145052203381516057),(101,708247487427826865469283)] (by decide +kernel) (by decide +kernel)

private theorem receipt_1_5_2451_0 : fastPhase (bank 1 5).shape 179808 2451 5 1 0 2 0 = 10389228435928942798994811 := p1 1 5 2451 5 1 0 2 0 357 10389228435928942798994811 [(128,6408993142969395638794560),(128,3257436730632932723978237),(101,722798562326614436222014)] (by decide +kernel) (by decide +kernel)

private theorem receipt_1_5_2451_1 : fastPhase (bank 1 5).shape 179808 2451 5 1 0 2 1 = 10325887599839421984685373 := p1 1 5 2451 5 1 0 2 1 357 10325887599839421984685373 [(128,6382320288734085698598656),(128,3235316447027482656389154),(101,708250864077853629697563)] (by decide +kernel) (by decide +kernel)

theorem receipt_1_5 : Checked (bank 1 5) 5 0 2 := by
  refine checked_from_values (bank 1 5) 5 0 2
    (P3_7_1.checked (bank 1 5) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1696_356)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_1_5_2450_0 receipt_1_5_2450_1 receipt_1_5_2451_0 receipt_1_5_2451_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_2_5_2450_0 : fastPhase (bank 2 5).shape 179808 2450 5 1 0 7 0 = 5436108136017215939125178 := p1 2 5 2450 5 1 0 7 0 357 5436108136017215939125178 [(128,3411858727849469148909792),(128,1667010265800433690856293),(101,357239142367313099359093)] (by decide +kernel) (by decide +kernel)

private theorem receipt_2_5_2450_1 : fastPhase (bank 2 5).shape 179808 2450 5 1 0 7 1 = 5401768628429436947972266 := p1 2 5 2450 5 1 0 7 1 357 5401768628429436947972266 [(128,3396614534488133778828000),(128,1655183393234793166366875),(101,349970700706510002777391)] (by decide +kernel) (by decide +kernel)

private theorem receipt_2_5_2451_0 : fastPhase (bank 2 5).shape 179808 2451 5 1 0 7 0 = 5436149767336616111148612 := p1 2 5 2451 5 1 0 7 0 357 5436149767336616111148612 [(128,3411887681369717465847168),(128,1667021242988189369814749),(101,357240842978709275486695)] (by decide +kernel) (by decide +kernel)

private theorem receipt_2_5_2451_1 : fastPhase (bank 2 5).shape 179808 2451 5 1 0 7 1 = 5401810051801327017808637 := p1 2 5 2451 5 1 0 7 1 357 5401810051801327017808637 [(128,3396643378906985105853440),(128,1655194302494868701617497),(101,349972370399473210337700)] (by decide +kernel) (by decide +kernel)

theorem receipt_2_5 : Checked (bank 2 5) 5 0 7 := by
  refine checked_from_values (bank 2 5) 5 0 7
    (P3_7_1.checked (bank 2 5) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1696_356)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_2_5_2450_0 receipt_2_5_2450_1 receipt_2_5_2451_0 receipt_2_5_2451_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_3_5_2450_0 : fastPhase (bank 3 5).shape 179808 2450 5 1 1 1 0 = 3305901041675462233518858 := p1 3 5 2450 5 1 1 1 0 371 3305901041675462233518858 [(128,2002337706231744488599104),(128,1037540374979901410258496),(115,266022960463816334661258)] (by decide +kernel) (by decide +kernel)

private theorem receipt_3_5_2450_1 : fastPhase (bank 3 5).shape 179808 2450 5 1 1 1 1 = 3286215749906943684588954 := p1 3 5 2450 5 1 1 1 1 371 3286215749906943684588954 [(128,1994198442291464857553664),(128,1030782063625501350488832),(115,261235243989977476546458)] (by decide +kernel) (by decide +kernel)

private theorem receipt_3_5_2451_0 : fastPhase (bank 3 5).shape 179808 2451 5 1 1 1 0 = 3305922857240819922986607 := p1 3 5 2451 5 1 1 1 0 371 3305922857240819922986607 [(128,2002353637784569493035680),(128,1037545580875453804825248),(115,266023638580796625125679)] (by decide +kernel) (by decide +kernel)

private theorem receipt_3_5_2451_1 : fastPhase (bank 3 5).shape 179808 2451 5 1 1 1 1 = 3286237444033824607421031 := p1 3 5 2451 5 1 1 1 1 371 3286237444033824607421031 [(128,1994214300409574594972448),(128,1030787232726483799915296),(115,261235910897766212533287)] (by decide +kernel) (by decide +kernel)

theorem receipt_3_5 : Checked (bank 3 5) 5 1 1 := by
  refine checked_from_values (bank 3 5) 5 1 1
    (P3_7_1.checked (bank 3 5) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1696_370)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_3_5_2450_0 receipt_3_5_2450_1 receipt_3_5_2451_0 receipt_3_5_2451_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_0_6_2450_0 : fastPhase (bank 0 6).shape 179808 2450 7 1 0 1 0 = 19553977320010893442592983 := p1 0 6 2450 7 1 0 1 0 381 19553977320010893442592983 [(128,11459665216898842677363924),(128,6236598670719537877127127),(125,1857713432392512888101932)] (by decide +kernel) (by decide +kernel)

private theorem receipt_0_6_2450_1 : fastPhase (bank 0 6).shape 179808 2450 7 1 0 1 1 = 19442831719816053981715861 := p1 0 6 2450 7 1 0 1 1 381 19442831719816053981715861 [(128,11415935605151277342811226),(128,6199521775715257592877143),(125,1827374338949519046027492)] (by decide +kernel) (by decide +kernel)

private theorem receipt_0_6_2451_0 : fastPhase (bank 0 6).shape 179808 2451 7 1 0 1 0 = 19554126589889537066116435 := p1 0 6 2451 7 1 0 1 0 381 19554126589889537066116435 [(128,11459763338842340494324141),(128,6236640685676523120212374),(125,1857722565370673451579920)] (by decide +kernel) (by decide +kernel)

private theorem receipt_0_6_2451_1 : fastPhase (bank 0 6).shape 179808 2451 7 1 0 1 1 = 19442980332611480567924023 := p1 0 6 2451 7 1 0 1 1 381 19442980332611480567924023 [(128,11416033416634243121612831),(128,6199563575080630204834400),(125,1827383340896607241476792)] (by decide +kernel) (by decide +kernel)

theorem receipt_0_6 : Checked (bank 0 6) 7 0 1 := by
  refine checked_from_values (bank 0 6) 7 0 1
    (P3_7_1.checked (bank 0 6) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1817_380)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_0_6_2450_0 receipt_0_6_2450_1 receipt_0_6_2451_0 receipt_0_6_2451_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_1_6_2450_0 : fastPhase (bank 1 6).shape 179808 2450 7 1 0 2 0 = 17552129200354321689534813 := p1 1 6 2450 7 1 0 2 0 381 17552129200354321689534813 [(128,10310957313739109964943419),(128,5584810702440441071192427),(125,1656361184174770653398967)] (by decide +kernel) (by decide +kernel)

private theorem receipt_1_6_2450_1 : fastPhase (bank 1 6).shape 179808 2450 7 1 0 2 1 = 17451900057738949794372939 := p1 1 6 2450 7 1 0 2 1 381 17451900057738949794372939 [(128,10271227059271715256784569),(128,5551404900808789995610422),(125,1629268097658444541977948)] (by decide +kernel) (by decide +kernel)

private theorem receipt_1_6_2451_0 : fastPhase (bank 1 6).shape 179808 2451 7 1 0 2 0 = 17552263266114195961140251 := p1 1 6 2451 7 1 0 2 0 381 17552263266114195961140251 [(128,10311045607233017135715431),(128,5584848330695690361740526),(125,1656369328185488463684294)] (by decide +kernel) (by decide +kernel)

private theorem receipt_1_6_2451_1 : fastPhase (bank 1 6).shape 179808 2451 7 1 0 2 1 = 17452033529313720845470353 := p1 1 6 2451 7 1 0 2 1 381 17452033529313720845470353 [(128,10271315070108348517534263),(128,5551442334603499069594158),(125,1629276124601873258341932)] (by decide +kernel) (by decide +kernel)

theorem receipt_1_6 : Checked (bank 1 6) 7 0 2 := by
  refine checked_from_values (bank 1 6) 7 0 2
    (P3_7_1.checked (bank 1 6) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1817_380)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_1_6_2450_0 receipt_1_6_2450_1 receipt_1_6_2451_0 receipt_1_6_2451_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_2_6_2450_0 : fastPhase (bank 2 6).shape 179808 2450 7 1 0 7 0 = 9148040231414163872590599 := p1 2 6 2450 7 1 0 7 0 381 9148040231414163872590599 [(128,5466932215542121176740832),(128,2859903006283074734818272),(125,821205009588967961031495)] (by decide +kernel) (by decide +kernel)

private theorem receipt_2_6_2450_1 : fastPhase (bank 2 6).shape 179808 2450 7 1 0 7 1 = 9094032446191885858170800 := p1 2 6 2450 7 1 0 7 1 381 9094032446191885858170800 [(128,5444392557363331364981984),(128,2842025550683108239768800),(125,807614338145446253420016)] (by decide +kernel) (by decide +kernel)

private theorem receipt_2_6_2451_0 : fastPhase (bank 2 6).shape 179808 2451 7 1 0 7 0 = 9148109887732351600248068 := p1 2 6 2451 7 1 0 7 0 381 9148109887732351600248068 [(128,5466978639147759070389504),(128,2859922198305934228022528),(125,821209050278658301836036)] (by decide +kernel) (by decide +kernel)

private theorem receipt_2_6_2451_1 : fastPhase (bank 2 6).shape 179808 2451 7 1 0 7 1 = 9094101778018522882470294 := p1 2 6 2451 7 1 0 7 1 381 9094101778018522882470294 [(128,5444438819802702060551360),(128,2842044638307351289863360),(125,807618319908469532055574)] (by decide +kernel) (by decide +kernel)

theorem receipt_2_6 : Checked (bank 2 6) 7 0 7 := by
  refine checked_from_values (bank 2 6) 7 0 7
    (P3_7_1.checked (bank 2 6) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1809_380)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_2_6_2450_0 receipt_2_6_2450_1 receipt_2_6_2451_0 receipt_2_6_2451_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_3_6_2450_0 : fastPhase (bank 3 6).shape 179808 2450 7 1 1 1 0 = 5210812080412182775220283 := p1 3 6 2450 7 1 1 1 0 396 5210812080412182775220283 [(128,3004829546063062633647840),(128,1654032814302081659043552),(128,548013547943333219954400),(12,3936172103705262574491)] (by decide +kernel) (by decide +kernel)

private theorem receipt_3_6_2450_1 : fastPhase (bank 3 6).shape 179808 2450 7 1 1 1 1 = 5181741346857207469082163 := p1 3 6 2450 7 1 1 1 1 396 5181741346857207469082163 [(128,2993513046940309123260000),(128,1644492282162548089253472),(128,540408130153612174327392),(12,3327887600738082241299)] (by decide +kernel) (by decide +kernel)

private theorem receipt_3_6_2451_0 : fastPhase (bank 3 6).shape 179808 2451 7 1 1 1 0 = 5210846261965325822296665 := p1 3 6 2451 7 1 1 1 0 396 5210846261965325822296665 [(128,3004853570773701018460320),(128,1654041450961600258191520),(128,548015064141691051786400),(12,3936176088333493858425)] (by decide +kernel) (by decide +kernel)

private theorem receipt_3_6_2451_1 : fastPhase (bank 3 6).shape 179808 2451 7 1 1 1 1 = 5181775350264056841123189 := p1 3 6 2451 7 1 1 1 1 396 5181775350264056841123189 [(128,2993536968785899666825120),(128,1644500864260301897306016),(128,540409626234659972759456),(12,3327890983195304232597)] (by decide +kernel) (by decide +kernel)

theorem receipt_3_6 : Checked (bank 3 6) 7 1 1 := by
  refine checked_from_values (bank 3 6) 7 1 1
    (P3_7_1.checked (bank 3 6) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1809_395)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_3_6_2450_0 receipt_3_6_2450_1 receipt_3_6_2451_0 receipt_3_6_2451_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_0_7_2450_0 : fastPhase (bank 0 7).shape 179808 2450 10 1 0 1 0 = 68098563057954525138433800 := p1 0 7 2450 10 1 0 1 0 481 68098563057954525138433800 [(128,33225226797870446085969216),(128,21400603597435232320132416),(128,11083290398962844416642233),(97,2389442263686002315689935)] (by decide +kernel) (by decide +kernel)

private theorem receipt_0_7_2450_1 : fastPhase (bank 0 7).shape 179808 2450 10 1 0 1 1 = 67791678812917116983835663 := p1 0 7 2450 10 1 0 1 1 481 67791678812917116983835663 [(128,33127966278235003604448000),(128,21315121702696534614725376),(128,11008784684441497906312857),(97,2339806147544080858349430)] (by decide +kernel) (by decide +kernel)

private theorem receipt_0_7_2451_0 : fastPhase (bank 0 7).shape 179808 2451 10 1 0 1 0 = 68099078361502239720707486 := p1 0 7 2451 10 1 0 1 0 481 68099078361502239720707486 [(128,33225513491798164568114336),(128,21400758287363038606816416),(128,11083353931208733895184778),(97,2389452651132302650591956)] (by decide +kernel) (by decide +kernel)

private theorem receipt_0_7_2451_1 : fastPhase (bank 0 7).shape 179808 2451 10 1 0 1 1 = 67792192316381973128588396 := p1 0 7 2451 10 1 0 1 1 481 67792192316381973128588396 [(128,33128252277452853911577440),(128,21315275863994240668914528),(128,11008847837331972461247654),(97,2339816337602906086848774)] (by decide +kernel) (by decide +kernel)

theorem receipt_0_7 : Checked (bank 0 7) 10 0 1 := by
  refine checked_from_values (bank 0 7) 10 0 1
    (P3_7_1.checked (bank 0 7) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_2285_480)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_0_7_2450_0 receipt_0_7_2450_1 receipt_0_7_2451_0 receipt_0_7_2451_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_1_7_2450_0 : fastPhase (bank 1 7).shape 179808 2450 10 1 0 2 0 = 61030634883643784652925160 := p1 1 7 2450 10 1 0 2 0 481 61030634883643784652925160 [(128,29866962288409774687199616),(128,19158611960474633537413504),(128,9881971926220123253632215),(97,2123088708539253174679825)] (by decide +kernel) (by decide +kernel)

private theorem receipt_1_7_2450_1 : fastPhase (bank 1 7).shape 179808 2450 10 1 0 2 1 = 60754226222661378576629608 := p1 1 7 2450 10 1 0 2 1 481 60754226222661378576629608 [(128,29778575601144918691826048),(128,19081473984551228769503616),(128,9815237129681518202191634),(97,2078939507283712913108310)] (by decide +kernel) (by decide +kernel)

private theorem receipt_1_7_2451_0 : fastPhase (bank 1 7).shape 179808 2451 10 1 0 2 0 = 61031096988769722934210100 := p1 1 7 2451 10 1 0 2 0 481 61031096988769722934210100 [(128,29867220018433980628466016),(128,19158750454271172178921824),(128,9882028577475275004616957),(97,2123097938589295122205303)] (by decide +kernel) (by decide +kernel)

private theorem receipt_1_7_2451_1 : fastPhase (bank 1 7).shape 179808 2451 10 1 0 2 1 = 60754686701658598477915846 := p1 1 7 2451 10 1 0 2 1 481 60754686701658598477915846 [(128,29778832698378462445850400),(128,19081612000638771889995552),(128,9815293440913217979331006),(97,2078948561728146162738888)] (by decide +kernel) (by decide +kernel)

theorem receipt_1_7 : Checked (bank 1 7) 10 0 2 := by
  refine checked_from_values (bank 1 7) 10 0 2
    (P3_7_1.checked (bank 1 7) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_2285_480)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_1_7_2450_0 receipt_1_7_2450_1 receipt_1_7_2451_0 receipt_1_7_2451_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_2_7_2450_0 : fastPhase (bank 2 7).shape 179808 2450 10 1 0 7 0 = 31912134718262615699599260 := p1 2 7 2450 10 1 0 7 0 481 31912134718262615699599260 [(128,15960216930366862953083616),(128,9936788818621334216819424),(128,4973928656283453169174545),(97,1041200312990965360521675)] (by decide +kernel) (by decide +kernel)

private theorem receipt_2_7_2450_1 : fastPhase (bank 2 7).shape 179808 2450 10 1 0 7 1 = 31762334011333382281139958 := p1 2 7 2450 10 1 0 7 1 481 31762334011333382281139958 [(128,15909302851855772261062368),(128,9894457626783006337173216),(128,4939195812269025382318014),(97,1019377720425578300586360)] (by decide +kernel) (by decide +kernel)

private theorem receipt_2_7_2451_0 : fastPhase (bank 2 7).shape 179808 2451 10 1 0 7 0 = 31912377427130504512244060 := p1 2 7 2451 10 1 0 7 0 481 31912377427130504512244060 [(128,15960354708828287542553216),(128,9936860686342842096380544),(128,4973957190525059091024192),(97,1041204841434315782286108)] (by decide +kernel) (by decide +kernel)

private theorem receipt_2_7_2451_1 : fastPhase (bank 2 7).shape 179808 2451 10 1 0 7 1 = 31762575820602980664323096 := p1 2 7 2451 10 1 0 7 1 481 31762575820602980664323096 [(128,15909440260223654956260800),(128,9894529229788211404504512),(128,4939224168663153020948886),(97,1019382161927961282608898)] (by decide +kernel) (by decide +kernel)

theorem receipt_2_7 : Checked (bank 2 7) 10 0 7 := by
  refine checked_from_values (bank 2 7) 10 0 7
    (P3_7_1.checked (bank 2 7) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_2285_480)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_2_7_2450_0 receipt_2_7_2450_1 receipt_2_7_2451_0 receipt_2_7_2451_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_3_7_2450_0 : fastPhase (bank 3 7).shape 179808 2450 10 1 1 1 0 = 19422444043526878095573150 := p1 3 7 2450 10 1 1 1 0 499 19422444043526878095573150 [(128,9331134885666287734607424),(128,6044219725276343182372416),(128,3203174470451069240774208),(115,843914962133177937819102)] (by decide +kernel) (by decide +kernel)

private theorem receipt_3_7_2450_1 : fastPhase (bank 3 7).shape 179808 2450 10 1 1 1 1 = 19336401685569101812190784 := p1 3 7 2450 10 1 1 1 1 499 19336401685569101812190784 [(128,9304137046989100146359808),(128,6020474186635685493825024),(128,3182915907811995739799040),(115,828874544132320432206912)] (by decide +kernel) (by decide +kernel)

private theorem receipt_3_7_2451_0 : fastPhase (bank 3 7).shape 179808 2451 10 1 1 1 0 = 19422571262310308517610250 := p1 3 7 2451 10 1 1 1 0 499 19422571262310308517610250 [(128,9331211724546745774428480),(128,6044255936878946900988224),(128,3203186886611811456373056),(115,843916714272804385820490)] (by decide +kernel) (by decide +kernel)

private theorem receipt_3_7_2451_1 : fastPhase (bank 3 7).shape 179808 2451 10 1 1 1 1 = 19336528377892653908904098 := p1 3 7 2451 10 1 1 1 1 499 19336528377892653908904098 [(128,9304213631572798190646464),(128,6020510239252160262534336),(128,3182928239581754768422080),(115,828876267485940687301218)] (by decide +kernel) (by decide +kernel)

theorem receipt_3_7 : Checked (bank 3 7) 10 1 1 := by
  refine checked_from_values (bank 3 7) 10 1 1
    (P3_7_1.checked (bank 3 7) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_2285_498)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_3_7_2450_0 receipt_3_7_2450_1 receipt_3_7_2451_0 receipt_3_7_2451_1 (by decide +kernel) (by decide +kernel)

def group2_stage (i : Fin 3) : Fin 17 :=
  ⟨5+i.val, by have := i.isLt; omega⟩

theorem group2_checked (rect : Fin 4) (i : Fin 3) :
    Checked (bank rect (group2_stage i)) (reserve (group2_stage i))
      (excess rect) (seed rect) := by
  fin_cases i
  · fin_cases rect
    · exact receipt_0_5
    · exact receipt_1_5
    · exact receipt_2_5
    · exact receipt_3_5
  · fin_cases rect
    · exact receipt_0_6
    · exact receipt_1_6
    · exact receipt_2_6
    · exact receipt_3_6
  · fin_cases rect
    · exact receipt_0_7
    · exact receipt_1_7
    · exact receipt_2_7
    · exact receipt_3_7

end Lower6961.Hi.RescueSource
