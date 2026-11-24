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

theorem moment_1696_356 : momentEstimate 1696 356 = 222371564601 := mkM 1696 356 222371564601 [(128,572684320),(128,3684337696),(128,9136834131),(128,15370032384),(128,20341757184),(128,23816115456),(128,25793107200),(128,26272732416),(128,25254991104),(128,22739883264),(128,18755777396),(128,13945647249),(128,9230875643),(128,5110148823),(128,2022537952),(128,324080352),(4,22031)] rfl rfl (by dsimp only [mblk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

theorem moment_1696_370 : momentEstimate 1696 370 = 229159736517 := mkM 1696 370 229159736517 [(128,572684320),(128,3684337696),(128,9141056804),(128,15557757376),(128,20767001024),(128,24420157888),(128,26517227968),(128,27058211264),(128,26043107776),(128,23471917504),(128,19393615038),(128,14532053576),(128,9746328986),(128,5521630460),(128,2297261808),(128,434348784),(18,1038245)] rfl rfl (by dsimp only [mblk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

theorem moment_1809_380 : momentEstimate 1809 380 = 287901786632 := mkM 1809 380 287901786632 [(128,613111200),(128,3963594144),(128,9896705511),(128,17097207360),(128,23183453760),(128,27671670336),(128,30561857088),(128,31854014016),(128,31548141120),(128,29644238400),(128,26142305856),(128,21163152440),(128,15641164329),(128,10359919872),(128,5784462598),(128,2356385168),(128,419948944),(13,454490)] rfl rfl (by dsimp only [mblk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

theorem moment_1809_395 : momentEstimate 1809 395 = 296724029248 := mkM 1809 395 296724029248 [(128,613111200),(128,3963594144),(128,9896719776),(128,17253050925),(128,23627260800),(128,28340839296),(128,31393473408),(128,32785163136),(128,32515908480),(128,30585709440),(128,26994566016),(128,21919153025),(128,16340444489),(128,10971561561),(128,6272279892),(128,2685846592),(128,561511488),(28,3835580)] rfl rfl (by dsimp only [mblk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

theorem moment_1817_380 : momentEstimate 1817 380 = 292013331876 := mkM 1817 380 292013331876 [(128,615973280),(128,3983364512),(128,9950161303),(128,17198059584),(128,23334244416),(128,27872399424),(128,30812524608),(128,32154619968),(128,31898685504),(128,30044721216),(128,26592727104),(128,21638440059),(128,16076646528),(128,10730530099),(128,6072063646),(128,2541701328),(128,494759120),(21,1710177)] rfl rfl (by dsimp only [mblk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

theorem moment_2285_480 : momentEstimate 2285 480 = 732176567216 := mkM 2285 480 732176567216 [(128,783404960),(128,5139931040),(128,13077344160),(128,23780618088),(128,35332736192),(128,45144212672),(128,52938228928),(128,58714784960),(128,62473880768),(128,64215516352),(128,63939691712),(128,61646406848),(128,57335661760),(128,51007456448),(128,42848244955),(128,34024165326),(128,25358865055),(128,17353338622),(128,10420160528),(128,5035269136),(128,1515991056),(77,90657650)] rfl rfl (by dsimp only [mblk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

theorem moment_2285_498 : momentEstimate 2285 498 = 753510622290 := mkM 2285 498 753510622290 [(128,783404960),(128,5139931040),(128,13077344160),(128,23789529417),(128,35672256512),(128,45924478976),(128,54083743744),(128,60150050816),(128,64123400192),(128,66003791872),(128,65791225856),(128,63485702144),(128,59087220736),(128,52595798457),(128,44296056302),(128,35392420168),(128,26610909096),(128,18448620482),(128,11312632000),(128,5685571776),(128,1888735424),(95,167798160)] rfl rfl (by dsimp only [mblk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem receipt_0_5_2450_0 : fastPhase (bank 0 5).shape 179818 2450 5 1 0 1 0 = 8554519691476315840829656 := mkP 0 5 2450 5 1 0 1 0 357 8554519691476315840829656 [(128,5266372858818355792619104),(128,2689077767632669709981916),(101,599069065025290338228636)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem receipt_0_5_2450_1 : fastPhase (bank 0 5).shape 179818 2450 5 1 0 1 1 = 8502584095642410391224265 := mkP 0 5 2450 5 1 0 1 1 357 8502584095642410391224265 [(128,5244645997940422156734560),(128,2670911566796758638743396),(101,587026530905229595746309)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem receipt_0_5_2451_0 : fastPhase (bank 0 5).shape 179818 2451 5 1 0 1 0 = 8554584876222285819480743 := mkP 0 5 2451 5 1 0 1 0 357 8554584876222285819480743 [(128,5266417508726703358216768),(128,2689095452846340930057992),(101,599071914649241531205983)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem receipt_0_5_2451_1 : fastPhase (bank 0 5).shape 179818 2451 5 1 0 1 1 = 8502648972971693235600927 := mkP 0 5 2451 5 1 0 1 1 357 8502648972971693235600927 [(128,5244690494911441839586048),(128,2670929148596349459499124),(101,587029329463901936515755)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

theorem receipt_0_5 : Checked (bank 0 5) 5 0 1 := by
  refine checked_from_values (bank 0 5) 5 0 1
    (P3_7_1.checked (bank 0 5) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1696_356)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_0_5_2450_0 receipt_0_5_2450_1 receipt_0_5_2451_0 receipt_0_5_2451_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_1_5_2450_0 : fastPhase (bank 1 5).shape 179818 2450 5 1 0 2 0 = 7662051405807558399606390 := mkP 1 5 2450 5 1 0 2 0 357 7662051405807558399606390 [(128,4730151235422864732870624),(128,2400110114062961614349742),(101,531790056321732052386024)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem receipt_1_5_2450_1 : fastPhase (bank 1 5).shape 179818 2450 5 1 0 2 1 = 7615265702243646391808451 := mkP 1 5 2450 5 1 0 2 1 357 7615265702243646391808451 [(128,4710402940695230968372320),(128,2383780837720766319621294),(101,521081923827649103814837)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem receipt_1_5_2451_0 : fastPhase (bank 1 5).shape 179818 2451 5 1 0 2 0 = 7662109831279941684895869 := mkP 1 5 2451 5 1 0 2 0 357 7662109831279941684895869 [(128,4730191343705300977284160),(128,2400125901377900902198886),(101,531792586196739805412823)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem receipt_1_5_2451_1 : fastPhase (bank 1 5).shape 179818 2451 5 1 0 2 1 = 7615323849844697617668668 := mkP 1 5 2451 5 1 0 2 1 357 7615323849844697617668668 [(128,4710442909611574934979456),(128,2383796531957850864495830),(101,521084408275271818193382)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

theorem receipt_1_5 : Checked (bank 1 5) 5 0 2 := by
  refine checked_from_values (bank 1 5) 5 0 2
    (P3_7_1.checked (bank 1 5) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1696_356)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_1_5_2450_0 receipt_1_5_2450_1 receipt_1_5_2451_0 receipt_1_5_2451_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_2_5_2450_0 : fastPhase (bank 2 5).shape 179818 2450 5 1 0 7 0 = 3997125330520491431162729 := mkP 2 5 2450 5 1 0 7 0 357 3997125330520491431162729 [(128,2517662224258935141304704),(128,1219971012616825683500688),(101,259492093644730606357337)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem receipt_2_5_2450_1 : fastPhase (bank 2 5).shape 179818 2450 5 1 0 7 1 = 3971690603408378370608963 := mkP 2 5 2450 5 1 0 7 1 357 3971690603408378370608963 [(128,2506253516053824564330240),(128,1211237014195257123447188),(101,254200073159296682831535)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem receipt_2_5_2451_0 : fastPhase (bank 2 5).shape 179818 2451 5 1 0 7 0 = 3997155966000559548200088 := mkP 2 5 2451 5 1 0 7 0 357 3997155966000559548200088 [(128,2517683589973845953144256),(128,1219979046868021888100612),(101,259493329158691706955220)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem receipt_2_5_2451_1 : fastPhase (bank 2 5).shape 179818 2451 5 1 0 7 1 = 3971721084256523561793802 := mkP 2 5 2451 5 1 0 7 1 357 3971721084256523561793802 [(128,2506274799900998509473920),(128,1211244998208647899086660),(101,254201286146877153233222)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

theorem receipt_2_5 : Checked (bank 2 5) 5 0 7 := by
  refine checked_from_values (bank 2 5) 5 0 7
    (P3_7_1.checked (bank 2 5) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1696_356)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_2_5_2450_0 receipt_2_5_2450_1 receipt_2_5_2451_0 receipt_2_5_2451_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_3_5_2450_0 : fastPhase (bank 3 5).shape 179818 2450 5 1 1 1 0 = 2804351700201982324077663 := mkP 3 5 2450 5 1 1 1 0 371 2804351700201982324077663 [(128,1699195594012813670645664),(128,879752464607651577556896),(115,225403641581517075875103)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem receipt_3_5_2450_1 : fastPhase (bank 3 5).shape 179818 2450 5 1 1 1 1 = 2787640305953254664826564 := mkP 3 5 2450 5 1 1 1 1 371 2787640305953254664826564 [(128,1692277823206728524042784),(128,874016506691877625438752),(115,221345976054648515345028)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem receipt_3_5_2451_0 : fastPhase (bank 3 5).shape 179818 2451 5 1 1 1 0 = 2804370206890151582549867 := mkP 3 5 2451 5 1 1 1 0 371 2804370206890151582549867 [(128,1699209112332000741174560),(128,879756878444753846738208),(115,225404216113396994637099)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem receipt_3_5_2451_1 : fastPhase (bank 3 5).shape 179818 2451 5 1 1 1 1 = 2787658709521895737650591 := mkP 3 5 2451 5 1 1 1 1 371 2787658709521895737650591 [(128,1692291279129856255222368),(128,874020889305391451435616),(115,221346541086648030992607)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

theorem receipt_3_5 : Checked (bank 3 5) 5 1 1 := by
  refine checked_from_values (bank 3 5) 5 1 1
    (P3_7_1.checked (bank 3 5) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1696_370)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_3_5_2450_0 receipt_3_5_2450_1 receipt_3_5_2451_0 receipt_3_5_2451_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_0_6_2450_0 : fastPhase (bank 0 6).shape 179818 2450 7 1 0 1 0 = 14203195894966293918639634 := mkP 0 6 2450 7 1 0 1 0 381 14203195894966293918639634 [(128,8326892833586474338749134),(128,4528337992869750663783147),(125,1347965068510068916107353)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem receipt_0_6_2450_1 : fastPhase (bank 0 6).shape 179818 2450 7 1 0 1 1 = 14122406411520464907003874 := mkP 0 6 2450 7 1 0 1 1 381 14122406411520464907003874 [(128,8295069630442242270932501),(128,4501391216752109945653643),(125,1325945564326112690417730)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem receipt_0_6_2451_0 : fastPhase (bank 0 6).shape 179818 2451 7 1 0 1 0 = 14203304323202123873127100 := mkP 0 6 2451 7 1 0 1 0 381 14203304323202123873127100 [(128,8326964126239479703776086),(128,4528368500964527530876942),(125,1347971695998116638474072)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem receipt_0_6_2451_1 : fastPhase (bank 0 6).shape 179818 2451 7 1 0 1 1 = 14122514361934741995758182 := mkP 0 6 2451 7 1 0 1 1 381 14122514361934741995758182 [(128,8295140697106849112304154),(128,4501421568127157635391780),(125,1325952096700735248062248)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

theorem receipt_0_6 : Checked (bank 0 6) 7 0 1 := by
  refine checked_from_values (bank 0 6) 7 0 1
    (P3_7_1.checked (bank 0 6) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1817_380)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_0_6_2450_0 receipt_0_6_2450_1 receipt_0_6_2451_0 receipt_0_6_2451_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_1_6_2450_0 : fastPhase (bank 1 6).shape 179818 2450 7 1 0 2 0 = 12740058421735180672947066 := mkP 1 6 2450 7 1 0 2 0 381 12740058421735180672947066 [(128,7489961828068264175057100),(128,4050504021976830403403520),(125,1199592571690086094486446)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem receipt_1_6_2450_1 : fastPhase (bank 1 6).shape 179818 2450 7 1 0 2 1 = 12667197471010322401666873 := mkP 1 6 2450 7 1 0 2 1 381 12667197471010322401666873 [(128,7461009755579872232776779),(128,4026227014665339160876663),(125,1179960700765111008013431)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem receipt_1_6_2451_0 : fastPhase (bank 1 6).shape 179818 2451 7 1 0 2 0 = 12740155746249273733198295 := mkP 1 6 2451 7 1 0 2 0 381 12740155746249273733198295 [(128,7490025961287949747761902),(128,4050531314488213120365882),(125,1199598470473110865070511)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem receipt_1_6_2451_1 : fastPhase (bank 1 6).shape 179818 2451 7 1 0 2 1 = 12667294363199396347499826 := mkP 1 6 2451 7 1 0 2 1 381 12667294363199396347499826 [(128,7461073682697652225412889),(128,4026254165800774743099993),(125,1179966514700969378986944)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

theorem receipt_1_6 : Checked (bank 1 6) 7 0 2 := by
  refine checked_from_values (bank 1 6) 7 0 2
    (P3_7_1.checked (bank 1 6) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1817_380)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_1_6_2450_0 receipt_1_6_2450_1 receipt_1_6_2451_0 receipt_1_6_2451_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_2_6_2450_0 : fastPhase (bank 2 6).shape 179818 2450 7 1 0 7 0 = 6597894823891806893819304 := mkP 2 6 2450 7 1 0 7 0 381 6597894823891806893819304 [(128,3957884638209880459843776),(128,2054432567061033905854656),(125,585577618620892528120872)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem receipt_2_6_2450_1 : fastPhase (bank 2 6).shape 179818 2450 7 1 0 7 1 = 6558655969857571364193435 := mkP 2 6 2450 7 1 0 7 1 381 6558655969857571364193435 [(128,3941330501113129168772736),(128,2041465023907748786749056),(125,575860444836693408671643)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem receipt_2_6_2451_0 : fastPhase (bank 2 6).shape 179818 2451 7 1 0 7 0 = 6597945102546149428245821 := mkP 2 6 2451 7 1 0 7 0 381 6597945102546149428245821 [(128,3957918247569141007297472),(128,2054446354544988267154368),(125,585580500432020153793981)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem receipt_2_6_2451_1 : fastPhase (bank 2 6).shape 179818 2451 7 1 0 7 1 = 6558706011814946038543269 := mkP 2 6 2451 7 1 0 7 1 381 6558706011814946038543269 [(128,3941363991784059672408768),(128,2041478735549343693992640),(125,575863284481542672141861)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

theorem receipt_2_6 : Checked (bank 2 6) 7 0 7 := by
  refine checked_from_values (bank 2 6) 7 0 7
    (P3_7_1.checked (bank 2 6) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1809_380)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_2_6_2450_0 receipt_2_6_2450_1 receipt_2_6_2451_0 receipt_2_6_2451_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_3_6_2450_0 : fastPhase (bank 3 6).shape 179818 2450 7 1 1 1 0 = 4396301728326338613804846 := mkP 3 6 2450 7 1 1 1 0 396 4396301728326338613804846 [(128,2536149448231282916172864),(128,1394982451731266253464640),(128,461854288273049926476864),(12,3315540090739517690478)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem receipt_3_6_2450_1 : fastPhase (bank 3 6).shape 179818 2450 7 1 1 1 1 = 4371756511069034879214456 := mkP 3 6 2450 7 1 1 1 1 396 4371756511069034879214456 [(128,2526582963447987035416704),(128,1386927954258189667551360),(128,455442438728077550872704),(12,2803154634780625373688)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem receipt_3_6_2451_0 : fastPhase (bank 3 6).shape 179818 2451 7 1 1 1 0 = 4396330568241450549493068 := mkP 3 6 2451 7 1 1 1 0 396 4396330568241450549493068 [(128,2536169723672145719388672),(128,1394989735117253974919680),(128,461855566005329930496512),(12,3315543446720924688204)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem receipt_3_6_2451_1 : fastPhase (bank 3 6).shape 179818 2451 7 1 1 1 1 = 4371785200530444340637202 := mkP 3 6 2451 7 1 1 1 1 396 4371785200530444340637202 [(128,2526603151957056454510528),(128,1386935191589207441065920),(128,455443699500598301018048),(12,2803157483582144042706)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

theorem receipt_3_6 : Checked (bank 3 6) 7 1 1 := by
  refine checked_from_values (bank 3 6) 7 1 1
    (P3_7_1.checked (bank 3 6) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1809_395)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_3_6_2450_0 receipt_3_6_2450_1 receipt_3_6_2451_0 receipt_3_6_2451_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_0_7_2450_0 : fastPhase (bank 0 7).shape 179818 2450 10 1 0 1 0 = 50367166452673316929916141 := mkP 0 7 2450 10 1 0 1 0 481 50367166452673316929916141 [(128,24584898718040265012471072),(128,15825856687831806259090720),(128,8191329655239327130465960),(97,1765081391561918527888389)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem receipt_0_7_2450_1 : fastPhase (bank 0 7).shape 179818 2450 10 1 0 1 1 = 50140023241760492660820634 := mkP 0 7 2450 10 1 0 1 1 481 50140023241760492660820634 [(128,24512816476225690613210528),(128,15762569033411482892594592),(128,8136228089871112776076807),(97,1728409642252206378938707)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem receipt_0_7_2451_0 : fastPhase (bank 0 7).shape 179818 2451 10 1 0 1 0 = 50367547571470666262691449 := mkP 0 7 2451 10 1 0 1 0 481 50367547571470666262691449 [(128,24585110831425458731690112),(128,15825971068133049560246400),(128,8191376606424821916950480),(97,1765089065487336053804457)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem receipt_0_7_2451_1 : fastPhase (bank 0 7).shape 179818 2451 10 1 0 1 1 = 50140403027746205786025948 := mkP 0 7 2451 10 1 0 1 1 481 50140403027746205786025948 [(128,24513028074625856769311040),(128,15762683022299975113695552),(128,8136274760491599092021816),(97,1728417170328774810997540)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

theorem receipt_0_7 : Checked (bank 0 7) 10 0 1 := by
  refine checked_from_values (bank 0 7) 10 0 1
    (P3_7_1.checked (bank 0 7) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_2285_480)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_0_7_2450_0 receipt_0_7_2450_1 receipt_0_7_2451_0 receipt_0_7_2451_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_1_7_2450_0 : fastPhase (bank 1 7).shape 179818 2450 10 1 0 2 0 = 45107528284356220619346122 := mkP 1 7 2450 10 1 0 2 0 481 45107528284356220619346122 [(128,22095141051522595499634336),(128,14155292929741377213709984),(128,7292105653579176245076616),(97,1564988649513071660925186)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem receipt_1_7_2450_1 : fastPhase (bank 1 7).shape 179818 2450 10 1 0 2 1 = 44902921138723504959669685 := mkP 1 7 2450 10 1 0 2 1 481 44902921138723504959669685 [(128,22029535589404522284221408),(128,14098160068050623825466336),(128,7242791006198434435826359),(97,1532434475069924414155582)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem receipt_1_7_2451_0 : fastPhase (bank 1 7).shape 179818 2451 10 1 0 2 0 = 45107869849257020832396509 := mkP 1 7 2451 10 1 0 2 0 481 45107869849257020832396509 [(128,22095331695751978742029536),(128,14155395244455337084103904),(128,7292147455108527491902835),(97,1564995453941177514360234)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem receipt_1_7_2451_1 : fastPhase (bank 1 7).shape 179818 2451 10 1 0 2 1 = 44903261498917866263826867 := mkP 1 7 2451 10 1 0 2 1 481 44903261498917866263826867 [(128,22029725763663908254259040),(128,14098262028834239557322592),(128,7242832556426918501270672),(97,1532441149992799950974563)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

theorem receipt_1_7 : Checked (bank 1 7) 10 0 2 := by
  refine checked_from_values (bank 1 7) 10 0 2
    (P3_7_1.checked (bank 1 7) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_2285_480)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_1_7_2450_0 receipt_1_7_2450_1 receipt_1_7_2451_0 receipt_1_7_2451_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_2_7_2450_0 : fastPhase (bank 2 7).shape 179818 2450 10 1 0 7 0 = 23514829866249210690704252 := mkP 2 7 2450 10 1 0 7 0 481 23514829866249210690704252 [(128,11812916372601948933191136),(128,7309377736646140140996064),(128,3635700973878891761774761),(97,756834783122229854742291)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem receipt_2_7_2450_1 : fastPhase (bank 2 7).shape 179818 2450 10 1 0 7 1 = 23403636380810013504823270 := mkP 2 7 2450 10 1 0 7 1 481 23403636380810013504823270 [(128,11774673304023108320389088),(128,7277882524164802132563936),(128,3610135224649961101255594),(97,740945327972141950614652)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem receipt_2_7_2451_0 : fastPhase (bank 2 7).shape 179818 2451 10 1 0 7 0 = 23515008852342452643850649 := mkP 2 7 2451 10 1 0 7 0 481 23515008852342452643850649 [(128,11813018344369169796003936),(128,7309430600408371509823584),(128,3635721832202077027821635),(97,756838075362834310201494)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem receipt_2_7_2451_1 : fastPhase (bank 2 7).shape 179818 2451 10 1 0 7 1 = 23403814696494510814453527 := mkP 2 7 2451 10 1 0 7 1 481 23403814696494510814453527 [(128,11774774997046245758041440),(128,7277935190623931240975712),(128,3610155951942191899417427),(97,740948556882141916018948)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

theorem receipt_2_7 : Checked (bank 2 7) 10 0 7 := by
  refine checked_from_values (bank 2 7) 10 0 7
    (P3_7_1.checked (bank 2 7) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_2285_480)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_2_7_2450_0 receipt_2_7_2450_1 receipt_2_7_2451_0 receipt_2_7_2451_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_3_7_2450_0 : fastPhase (bank 3 7).shape 179818 2450 10 1 1 1 0 = 16493819165191460989980675 := mkP 3 7 2450 10 1 1 1 0 499 16493819165191460989980675 [(128,7927813637969602186114848),(128,5132104817949059298043680),(128,2718154755450730055554848),(115,715745953822069450267299)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem receipt_3_7_2450_1 : fastPhase (bank 3 7).shape 179818 2450 10 1 1 1 1 = 16420695555089080879165740 := mkP 3 7 2450 10 1 1 1 1 499 16420695555089080879165740 [(128,7904838526198421845660128),(128,5111918395072144394600928),(128,2700951172687127361761760),(115,702987461131387277142924)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem receipt_3_7_2451_0 : fastPhase (bank 3 7).shape 179818 2451 10 1 1 1 0 = 16493927206144539845659775 := mkP 3 7 2451 10 1 1 1 0 499 16493927206144539845659775 [(128,7927878913911510721149344),(128,5132135561874811695868320),(128,2718165290630631435901344),(115,715747439727585992740767)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem receipt_3_7_2451_1 : fastPhase (bank 3 7).shape 179818 2451 10 1 1 1 1 = 16420803148508990313086280 := mkP 3 7 2451 10 1 1 1 1 499 16420803148508990313086280 [(128,7904903585804085590653920),(128,5111949003873149144738784),(128,2700961636212432585612256),(115,702988922619322992081320)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

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
