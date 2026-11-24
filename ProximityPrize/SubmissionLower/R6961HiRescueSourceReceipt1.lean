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

theorem moment_977_207 : momentEstimate 977 207 = 24758176234 := mkM 977 207 24758176234 [(128,315454880),(128,1893094372),(128,3762297344),(128,4827257344),(128,5019802112),(128,4339931648),(128,2905553180),(128,1377948994),(128,313825184),(32,3011176)] rfl rfl (by dsimp only [mblk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

theorem moment_1047_222 : momentEstimate 1047 222 = 32653699308 := mkM 1047 222 32653699308 [(128,340498080),(128,2075230592),(128,4311457024),(128,5736373504),(128,6225960192),(128,5780217088),(128,4419886184),(128,2600283532),(128,1026138287),(117,137654825)] rfl rfl (by dsimp only [mblk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

theorem moment_1117_237 : momentEstimate 1117 237 = 42302192650 := mkM 1117 237 42302192650 [(128,365541280),(128,2252469787),(128,4866007104),(128,6688972864),(128,7513694272),(128,7340171328),(128,6168649768),(128,4198892547),(128,2189402175),(128,679563600),(74,38827925)] rfl rfl (by dsimp only [mblk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

theorem moment_1326_281 : momentEstimate 1326 281 = 83828003187 := mkM 1326 281 83828003187 [(128,440313120),(128,2769958176),(128,6492999306),(128,9717503424),(128,11761980864),(128,12623664576),(128,12302554560),(128,10798650816),(128,8203180395),(128,5254501290),(128,2634292110),(128,787344864),(71,41059686)] rfl rfl (by dsimp only [mblk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

theorem moment_1327_281 : momentEstimate 1327 281 = 84031339757 := mkM 1327 281 84031339757 [(128,440670880),(128,2772429472),(128,6499499186),(128,9728620992),(128,11777718720),(128,12644022720),(128,12327532992),(128,10828249536),(128,8234870103),(128,5281874916),(128,2654626290),(128,798423904),(72,42800046)] rfl rfl (by dsimp only [mblk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

theorem moment_1341_282 : momentEstimate 1341 282 = 87154749585 := mkM 1341 282 87154749585 [(128,445679520),(128,2807027616),(128,6595706731),(128,9903134464),(128,12026730240),(128,12963337984),(128,12712957696),(128,11275589376),(128,8711118963),(128,5697061300),(128,2967083923),(128,974195776),(87,75125996)] rfl rfl (by dsimp only [mblk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

theorem moment_1387_302 : momentEstimate 1387 302 = 102461756220 := mkM 1387 302 102461756220 [(128,462136480),(128,2920707232),(128,6982836384),(128,10787226624),(128,13338903552),(128,14619706368),(128,14629635072),(128,13368689664),(128,10858832125),(128,7630480965),(128,4503008202),(128,1955193296),(128,402271696),(25,2128560)] rfl rfl (by dsimp only [mblk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

theorem moment_1392_291 : momentEstimate 1392 291 = 100699468110 := mkM 1392 291 100699468110 [(128,463925280),(128,2933063712),(128,6972032551),(128,10645366912),(128,13102016640),(128,14333929600),(128,14341105792),(128,13123545216),(128,10691106230),(128,7487810802),(128,4379387141),(128,1864956928),(128,360231936),(19,989370)] rfl rfl (by dsimp only [mblk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem receipt_0_1_2450_0 : fastPhase (bank 0 1).shape 179818 2450 1 1 0 1 0 = 1798271468830697375482614 := mkP 0 1 2450 1 1 0 1 0 282 1798271468830697375482614 [(128,1306787420685402189138185),(128,478304889899145883401281),(26,13179158246149302943148)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem receipt_0_1_2450_1 : fastPhase (bank 0 1).shape 179818 2450 1 1 0 1 1 = 1784439727544759707975448 := mkP 0 1 2450 1 1 0 1 1 282 1784439727544759707975448 [(128,1299609452915071014043889),(128,472635364441729464432011),(26,12194910187959229499548)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem receipt_0_1_2451_0 : fastPhase (bank 0 1).shape 179818 2451 1 1 0 1 0 = 1798285403123355511179538 := mkP 0 1 2451 1 1 0 1 0 282 1798285403123355511179538 [(128,1306798444794119593014198),(128,478307748254449906344344),(26,13179210074786011820996)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem receipt_0_1_2451_1 : fastPhase (bank 0 1).shape 179818 2451 1 1 0 1 1 = 1784453578846422268772174 := mkP 0 1 2451 1 1 0 1 1 282 1784453578846422268772174 [(128,1299620426825328922104302),(128,472638193707626701513096),(26,12194958313466645154776)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

theorem receipt_0_1 : Checked (bank 0 1) 1 0 1 := by
  refine checked_from_values (bank 0 1) 1 0 1
    (P3_7_1.checked (bank 0 1) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1327_281)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_0_1_2450_0 receipt_0_1_2450_1 receipt_0_1_2451_0 receipt_0_1_2451_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_1_1_2450_0 : fastPhase (bank 1 1).shape 179818 2450 1 1 0 2 0 = 1607492493728774780557434 := mkP 1 1 2450 1 1 0 2 0 282 1607492493728774780557434 [(128,1170790632601895559830064),(128,425061275359410302835786),(26,11640585767468917891584)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem receipt_1_1_2450_1 : fastPhase (bank 1 1).shape 179818 2450 1 1 0 2 1 = 1595052668264467695754680 := mkP 1 1 2450 1 1 0 2 1 282 1595052668264467695754680 [(128,1164283115307197094078342),(128,419998809504023043770526),(26,10770743453247557905812)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem receipt_1_1_2451_0 : fastPhase (bank 1 1).shape 179818 2451 1 1 0 2 0 = 1607504959259579989988819 := mkP 1 1 2451 1 1 0 2 0 282 1607504959259579989988819 [(128,1170800511460308944437409),(128,425063816253021709200714),(26,11640631546249336350696)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem receipt_1_1_2451_1 : fastPhase (bank 1 1).shape 179818 2451 1 1 0 2 1 = 1595065058883703635160092 := mkP 1 1 2451 1 1 0 2 1 282 1595065058883703635160092 [(128,1164292948533834755343318),(128,420001324390731559014630),(26,10770785959137320802144)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

theorem receipt_1_1 : Checked (bank 1 1) 1 0 2 := by
  refine checked_from_values (bank 1 1) 1 0 2
    (P3_7_1.checked (bank 1 1) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1327_281)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_1_1_2450_0 receipt_1_1_2450_1 receipt_1_1_2451_0 receipt_1_1_2451_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_2_1_2450_0 : fastPhase (bank 2 1).shape 179818 2450 1 1 0 7 0 = 827514966999525252398202 := mkP 2 1 2450 1 1 0 7 0 282 827514966999525252398202 [(128,612624699789687795413553),(128,209417852394986603633433),(26,5472414814850853351216)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem receipt_2_1_2450_1 : fastPhase (bank 2 1).shape 179818 2450 1 1 0 7 1 = 820823641470365058995868 := mkP 2 1 2450 1 1 0 7 1 282 820823641470365058995868 [(128,608927711893836718452153),(128,206834255217484279019523),(26,5061674359044061524192)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem receipt_2_1_2451_0 : fastPhase (bank 2 1).shape 179818 2451 1 1 0 7 0 = 827521419931808121025226 := mkP 2 1 2451 1 1 0 7 0 282 827521419931808121025226 [(128,612629876680387891929926),(128,209419106912486331507192),(26,5472436338933897588108)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem receipt_2_1_2451_1 : fastPhase (bank 2 1).shape 179818 2451 1 1 0 7 1 = 820830053078428576401498 := mkP 2 1 2451 1 1 0 7 1 282 820830053078428576401498 [(128,608932862398724962997178),(128,206835496342770161430816),(26,5061694336933451973504)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

theorem receipt_2_1 : Checked (bank 2 1) 1 0 7 := by
  refine checked_from_values (bank 2 1) 1 0 7
    (P3_7_1.checked (bank 2 1) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1327_281)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_2_1_2450_0 receipt_2_1_2450_1 receipt_2_1_2451_0 receipt_2_1_2451_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_3_1_2450_0 : fastPhase (bank 3 1).shape 179818 2450 1 1 1 1 0 = 130541895149702324392104 := mkP 3 1 2450 1 1 1 1 0 208 130541895149702324392104 [(128,113853269827731317923392),(80,16688625321971006468712)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem receipt_3_1_2450_1 : fastPhase (bank 3 1).shape 179818 2450 1 1 1 1 1 = 129164674815845409765024 := mkP 3 1 2450 1 1 1 1 1 208 129164674815845409765024 [(128,112908630527981939135232),(80,16256044287863470629792)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem receipt_3_1_2451_0 : fastPhase (bank 3 1).shape 179818 2451 1 1 1 1 0 = 130542775516255871336568 := mkP 3 1 2451 1 1 1 1 0 208 130542775516255871336568 [(128,113854097096826029732544),(80,16688678419429841604024)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem receipt_3_1_2451_1 : fastPhase (bank 3 1).shape 179818 2451 1 1 1 1 1 = 129165546474333799149720 := mkP 3 1 2451 1 1 1 1 1 208 129165546474333799149720 [(128,112909450361934520228800),(80,16256096112399278920920)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

theorem receipt_3_1 : Checked (bank 3 1) 1 1 1 := by
  refine checked_from_values (bank 3 1) 1 1 1
    (P3_7_1.checked (bank 3 1) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_977_207)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_3_1_2450_0 receipt_3_1_2450_1 receipt_3_1_2451_0 receipt_3_1_2451_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_0_2_2450_0 : fastPhase (bank 0 2).shape 179818 2450 2 1 0 1 0 = 2138191607072845464118874 := mkP 0 2 2450 2 1 0 1 0 283 2138191607072845464118874 [(128,1549265325809802328453344),(128,572104428967471743105291),(27,16821852295571392560239)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem receipt_0_2_2450_1 : fastPhase (bank 0 2).shape 179818 2450 2 1 0 1 1 = 2121826503742135627424731 := mkP 0 2 2450 2 1 0 1 1 283 2121826503742135627424731 [(128,1540816500301339036397280),(128,565399747847418384349660),(27,15610255593378206677791)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem receipt_0_2_2451_0 : fastPhase (bank 0 2).shape 179818 2451 2 1 0 1 0 = 2138207996071347421916198 := mkP 0 2 2451 2 1 0 1 0 283 2138207996071347421916198 [(128,1549278232261398262131904),(128,572107844629606914847130),(27,16821919180342244937164)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem receipt_0_2_2451_1 : fastPhase (bank 0 2).shape 179818 2451 2 1 0 1 1 = 2121842795177061569822291 := mkP 0 2 2451 2 1 0 1 1 283 2121842795177061569822291 [(128,1540829348274027231452736),(128,565403129032135967872349),(27,15610317870898370497206)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

theorem receipt_0_2 : Checked (bank 0 2) 2 0 1 := by
  refine checked_from_values (bank 0 2) 2 0 1
    (P3_7_1.checked (bank 0 2) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1341_282)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_0_2_2450_0 receipt_0_2_2450_1 receipt_0_2_2451_0 receipt_0_2_2451_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_1_2_2450_0 : fastPhase (bank 1 2).shape 179818 2450 2 1 0 2 0 = 1914090563202849681057834 := mkP 1 2 2450 2 1 0 2 0 283 1914090563202849681057834 [(128,1389850925683001920747200),(128,509348637490405708668435),(27,14891000029442051642199)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem receipt_1_2_2450_1 : fastPhase (bank 1 2).shape 179818 2450 2 1 0 2 1 = 1899356632354088796721410 := mkP 1 2 2450 2 1 0 2 1 283 1899356632354088796721410 [(128,1382186407264517800148160),(128,503352349025511216321063),(27,13817876064059780252187)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem receipt_1_2_2451_0 : fastPhase (bank 1 2).shape 179818 2451 2 1 0 2 0 = 1914105244753687327568837 := mkP 1 2 2451 2 1 0 2 0 283 1914105244753687327568837 [(128,1389862506251182649421600),(128,509351679264518910606191),(27,14891059237985767541046)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem receipt_1_2_2451_1 : fastPhase (bank 1 2).shape 179818 2451 2 1 0 2 1 = 1899371225771771815839323 := mkP 1 2 2451 2 1 0 2 1 283 1899371225771771815839323 [(128,1382197934650276375239776),(128,503355359929826642536263),(27,13817931191668798063284)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

theorem receipt_1_2 : Checked (bank 1 2) 2 0 2 := by
  refine checked_from_values (bank 1 2) 2 0 2
    (P3_7_1.checked (bank 1 2) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1341_282)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_1_2_2450_0 receipt_1_2_2450_1 receipt_1_2_2451_0 receipt_1_2_2451_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_2_2_2450_0 : fastPhase (bank 2 2).shape 179818 2450 2 1 0 7 0 = 994803353443501193853269 := mkP 2 2 2450 2 1 0 7 0 283 994803353443501193853269 [(128,733520981770712722222080),(128,254168146249009982659260),(27,7114225423778488971929)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem receipt_2_2_2450_1 : fastPhase (bank 2 2).shape 179818 2450 2 1 0 7 1 = 986824532346155967749875 := mkP 2 2 2450 2 1 0 7 1 283 986824532346155967749875 [(128,729150396352089726384960),(128,251074789751826792467338),(27,6599346242239448897577)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem receipt_2_2_2451_0 : fastPhase (bank 2 2).shape 179818 2451 2 1 0 7 0 = 994811022612172064964887 := mkP 2 2 2451 2 1 0 7 0 283 994811022612172064964887 [(128,733527101855775357088480),(128,254169667041996906343001),(27,7114253714399801533406)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem receipt_2_2_2451_1 : fastPhase (bank 2 2).shape 179818 2451 2 1 0 7 1 = 986832152670873404044553 := mkP 2 2 2451 2 1 0 7 1 283 986832152670873404044553 [(128,729156485608502459604576),(128,251076294488416287381863),(27,6599372573954657058114)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

theorem receipt_2_2 : Checked (bank 2 2) 2 0 7 := by
  refine checked_from_values (bank 2 2) 2 0 7
    (P3_7_1.checked (bank 2 2) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1341_282)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_2_2_2450_0 receipt_2_2_2450_1 receipt_2_2_2451_0 receipt_2_2_2451_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_3_2_2450_0 : fastPhase (bank 3 2).shape 179818 2450 2 1 1 1 0 = 203386784496830054152200 := mkP 3 2 2450 2 1 1 1 0 223 203386784496830054152200 [(128,171171460707113143814368),(95,32215323789716910337832)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem receipt_3_2_2450_1 : fastPhase (bank 3 2).shape 179818 2450 2 1 1 1 1 = 201384798172743404113552 := mkP 3 2 2450 2 1 1 1 1 223 201384798172743404113552 [(128,169877080480014019108320),(95,31507717692729385005232)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem receipt_3_2_2451_0 : fastPhase (bank 3 2).shape 179818 2451 2 1 1 1 0 = 203388150587380519013736 := mkP 3 2 2451 2 1 1 1 0 223 203388150587380519013736 [(128,171172717900776400947040),(95,32215432686604118066696)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem receipt_3_2_2451_1 : fastPhase (bank 3 2).shape 179818 2451 2 1 1 1 1 = 201386151662762025008987 := mkP 3 2 2451 2 1 1 1 1 223 201386151662762025008987 [(128,169878327281412670822752),(95,31507824381349354186235)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

theorem receipt_3_2 : Checked (bank 3 2) 2 1 1 := by
  refine checked_from_values (bank 3 2) 2 1 1
    (P3_7_1.checked (bank 3 2) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1047_222)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_3_2_2450_0 receipt_3_2_2450_1 receipt_3_2_2451_0 receipt_3_2_2451_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_0_3_2450_0 : fastPhase (bank 0 3).shape 179818 2450 3 1 0 1 0 = 2407058204239783316699078 := mkP 0 3 2450 3 1 0 1 0 282 2407058204239783316699078 [(128,1748709362841206992608884),(128,640682570723987267249427),(26,17666270674589056840767)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem receipt_0_3_2450_1 : fastPhase (bank 0 3).shape 179818 2450 3 1 0 1 1 = 2388557512138481976923134 := mkP 0 3 2450 3 1 0 1 1 282 2388557512138481976923134 [(128,1739117820759212931803962),(128,633092685401265060424572),(26,16347005978003984694600)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem receipt_0_3_2451_0 : fastPhase (bank 0 3).shape 179818 2451 3 1 0 1 0 = 2407076716244539032849616 := mkP 0 3 2451 3 1 0 1 0 282 2407076716244539032849616 [(128,1748724014393957161126996),(128,640686362761677906582678),(26,17666339088903965139942)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem receipt_0_3_2451_1 : fastPhase (bank 0 3).shape 179818 2451 3 1 0 1 1 = 2388575914183237079467764 := mkP 0 3 2451 3 1 0 1 1 282 2388575914183237079467764 [(128,1739132405754508436700840),(128,633096438921400736395263),(26,16347069507327906371661)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

theorem receipt_0_3 : Checked (bank 0 3) 3 0 1 := by
  refine checked_from_values (bank 0 3) 3 0 1
    (P3_7_1.checked (bank 0 3) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1326_281)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_0_3_2450_0 receipt_0_3_2450_1 receipt_0_3_2451_0 receipt_0_3_2451_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_1_3_2450_0 : fastPhase (bank 1 3).shape 179818 2450 3 1 0 2 0 = 2152560954808560926066442 := mkP 1 3 2450 3 1 0 2 0 282 2152560954808560926066442 [(128,1566874985991797318398809),(128,570050123812226879026842),(26,15635845004536728640791)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem receipt_1_3_2450_1 : fastPhase (bank 1 3).shape 179818 2450 3 1 0 2 1 = 2135929014276747783635130 := mkP 1 3 2450 3 1 0 2 1 282 2135929014276747783635130 [(128,1558192235778954305244741),(128,563269148818224979206345),(26,14467629679568499184044)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem receipt_1_3_2451_0 : fastPhase (bank 1 3).shape 179818 2451 3 1 0 2 0 = 2152577520563968586853356 := mkP 1 3 2451 3 1 0 2 0 282 2152577520563968586853356 [(128,1566888116375345701347773),(128,570053498631899171226162),(26,15635905556723714279421)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem receipt_1_3_2451_1 : fastPhase (bank 1 3).shape 179818 2451 3 1 0 2 1 = 2135945480864515790747850 := mkP 1 3 2451 3 1 0 2 1 282 2135945480864515790747850 [(128,1558205305770498158772861),(128,563272489188177668690223),(26,14467685905839963284766)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

theorem receipt_1_3 : Checked (bank 1 3) 3 0 2 := by
  refine checked_from_values (bank 1 3) 3 0 2
    (P3_7_1.checked (bank 1 3) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1326_281)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_1_3_2450_0 receipt_1_3_2450_1 receipt_1_3_2451_0 receipt_1_3_2451_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_2_3_2450_0 : fastPhase (bank 2 3).shape 179818 2450 3 1 0 7 0 = 1109328357303300462167562 := mkP 2 3 2450 3 1 0 7 0 282 1109328357303300462167562 [(128,818991227628068097670575),(128,282883537520765076943980),(26,7453592154467287553007)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem receipt_2_3_2450_1 : fastPhase (bank 2 3).shape 179818 2450 3 1 0 7 1 = 1100424597071270786383038 := mkP 2 3 2450 3 1 0 7 1 282 1100424597071270786383038 [(128,814115315015905847659977),(128,279414690645733113590709),(26,6894591409631825132352)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem receipt_2_3_2451_0 : fastPhase (bank 2 3).shape 179818 2451 3 1 0 7 0 = 1109336936017021810113200 := mkP 2 3 2451 3 1 0 7 0 282 1109336936017021810113200 [(128,818998099627215395849561),(128,282885215366916466814832),(26,7453621022889947448807)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem receipt_2_3_2451_1 : fastPhase (bank 2 3).shape 179818 2451 3 1 0 7 1 = 1100433121505014251371238 := mkP 2 3 2451 3 1 0 7 1 282 1100433121505014251371238 [(128,814122152567818064226393),(128,279416350729978607387145),(26,6894618207217579757700)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

theorem receipt_2_3 : Checked (bank 2 3) 3 0 7 := by
  refine checked_from_values (bank 2 3) 3 0 7
    (P3_7_1.checked (bank 2 3) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1326_281)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_2_3_2450_0 receipt_2_3_2450_1 receipt_2_3_2451_0 receipt_2_3_2451_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_3_3_2450_0 : fastPhase (bank 3 3).shape 179818 2450 3 1 1 1 0 = 307541434270404278821660 := mkP 3 3 2450 3 1 1 1 0 238 307541434270404278821660 [(128,249699709861891586495520),(110,57841724408512692326140)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem receipt_3_3_2450_1 : fastPhase (bank 3 3).shape 179818 2450 3 1 1 1 1 = 304704298883554443695339 := mkP 3 3 2450 3 1 1 1 1 238 304704298883554443695339 [(128,247965355132507634539424),(110,56738943751046809155915)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem receipt_3_3_2451_0 : fastPhase (bank 3 3).shape 179818 2451 3 1 1 1 0 = 307543492605797146392260 := mkP 3 3 2451 3 1 1 1 0 238 307543492605797146392260 [(128,249701562544561057536480),(110,57841930061236088855780)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem receipt_3_3_2451_1 : fastPhase (bank 3 3).shape 179818 2451 3 1 1 1 1 = 304706339433814907557073 := mkP 3 3 2451 3 1 1 1 1 238 304706339433814907557073 [(128,247967193645879496514336),(110,56739145787935411042737)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

theorem receipt_3_3 : Checked (bank 3 3) 3 1 1 := by
  refine checked_from_values (bank 3 3) 3 1 1
    (P3_7_1.checked (bank 3 3) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1117_237)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_3_3_2450_0 receipt_3_3_2450_1 receipt_3_3_2451_0 receipt_3_3_2451_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_0_4_2450_0 : fastPhase (bank 0 4).shape 179818 2450 4 1 0 1 0 = 3320366378388911304702915 := mkP 0 4 2450 4 1 0 1 0 292 3320366378388911304702915 [(128,2355519915815845348489209),(128,921297718851207027648477),(36,43548743721858928565229)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem receipt_0_4_2450_1 : fastPhase (bank 0 4).shape 179818 2450 4 1 0 1 1 = 3295753511101570849904508 := mkP 0 4 2450 4 1 0 1 1 292 3295753511101570849904508 [(128,2343177511235378540104128),(128,911406615173928465587826),(36,41169384692263844212554)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem receipt_0_4_2451_0 : fastPhase (bank 0 4).shape 179818 2451 4 1 0 1 0 = 3320391825606994683751652 := mkP 0 4 2451 4 1 0 1 0 292 3320391825606994683751652 [(128,2355539634659573313850688),(128,921303270527373178215306),(36,43548920420048191685658)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem receipt_0_4_2451_1 : fastPhase (bank 0 4).shape 179818 2451 4 1 0 1 1 = 3295778811970590906634604 := mkP 0 4 2451 4 1 0 1 1 292 3295778811970590906634604 [(128,2343197144275707423533141),(128,911412115425482634999336),(36,41169552269400848102127)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

theorem receipt_0_4 : Checked (bank 0 4) 4 0 1 := by
  refine checked_from_values (bank 0 4) 4 0 1
    (P3_7_1.checked (bank 0 4) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1392_291)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_0_4_2450_0 receipt_0_4_2450_1 receipt_0_4_2451_0 receipt_0_4_2451_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_1_4_2450_0 : fastPhase (bank 1 4).shape 179818 2450 4 1 0 2 0 = 2979043181418407579860434 := mkP 1 4 2450 4 1 0 2 0 292 2979043181418407579860434 [(128,2117536279773404629197945),(128,822806935016207968083945),(36,38699966628794982578544)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem receipt_1_4_2450_1 : fastPhase (bank 1 4).shape 179818 2450 4 1 0 2 1 = 2956848667090100678241552 := mkP 1 4 2450 4 1 0 2 1 292 2956848667090100678241552 [(128,2106329810001839008024107),(128,813934678517553594705651),(36,36584178570708075511794)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem receipt_1_4_2451_0 : fastPhase (bank 1 4).shape 179818 2451 4 1 0 2 0 = 2979066027072012646376669 := mkP 1 4 2451 4 1 0 2 0 292 2979066027072012646376669 [(128,2117554009124643049342025),(128,822811894290601067737134),(36,38700123656768529297510)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem receipt_1_4_2451_1 : fastPhase (bank 1 4).shape 179818 2451 4 1 0 2 1 = 2956871380378439315182217 := mkP 1 4 2451 4 1 0 2 1 292 2956871380378439315182217 [(128,2106347461273936819843049),(128,813939591617196703334292),(36,36584327487305792004876)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

theorem receipt_1_4 : Checked (bank 1 4) 4 0 2 := by
  refine checked_from_values (bank 1 4) 4 0 2
    (P3_7_1.checked (bank 1 4) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1392_291)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_1_4_2450_0 receipt_1_4_2450_1 receipt_1_4_2451_0 receipt_1_4_2451_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_2_4_2450_0 : fastPhase (bank 2 4).shape 179818 2450 4 1 0 7 0 = 1570258479393270123243307 := mkP 2 4 2450 4 1 0 7 0 292 1570258479393270123243307 [(128,1131961424432138535406033),(128,419297704591770336973659),(36,18999350369361250863615)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem receipt_2_4_2450_1 : fastPhase (bank 2 4).shape 179818 2450 4 1 0 7 1 = 1558130078241973845147437 := mkP 2 4 2450 4 1 0 7 1 292 1558130078241973845147437 [(128,1125543439386174045265947),(128,414631025195889021931475),(36,17955613659910777950015)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem receipt_2_4_2451_0 : fastPhase (bank 2 4).shape 179818 2451 4 1 0 7 0 = 1570270575905899786834696 := mkP 2 4 2451 4 1 0 7 0 292 1570270575905899786834696 [(128,1131970912494435672138856),(128,419300235937471479491604),(36,18999427473992635204236)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem receipt_2_4_2451_1 : fastPhase (bank 2 4).shape 179818 2451 4 1 0 7 1 = 1558142100908904004888834 := mkP 2 4 2451 4 1 0 7 1 292 1558142100908904004888834 [(128,1125552882072033949487994),(128,414633532076331716480128),(36,17955686760538338920712)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

theorem receipt_2_4 : Checked (bank 2 4) 4 0 7 := by
  refine checked_from_values (bank 2 4) 4 0 7
    (P3_7_1.checked (bank 2 4) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1392_291)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_2_4_2450_0 receipt_2_4_2450_1 receipt_2_4_2451_0 receipt_2_4_2451_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_3_4_2450_0 : fastPhase (bank 3 4).shape 179818 2450 4 1 1 1 0 = 957997552471331675400972 := mkP 3 4 2450 4 1 1 1 0 303 957997552471331675400972 [(128,670006638508014377432352),(128,269374289155587019072800),(47,18616624807730278895820)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem receipt_3_4_2450_1 : fastPhase (bank 3 4).shape 179818 2450 4 1 1 1 1 = 951017782333332673425102 := mkP 3 4 2450 4 1 1 1 1 303 951017782333332673425102 [(128,666538860352068321059232),(128,266655948912881834316192),(47,17822973068382518049678)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem receipt_3_4_2451_0 : fastPhase (bank 3 4).shape 179818 2451 4 1 1 1 0 = 958003873841289270870756 := mkP 3 4 2451 4 1 1 1 0 303 958003873841289270870756 [(128,670011788503030526521696),(128,269375428563544093032800),(47,18616656774714651316260)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem receipt_3_4_2451_1 : fastPhase (bank 3 4).shape 179818 2451 4 1 1 1 1 = 951024060640060865139815 := mkP 3 4 2451 4 1 1 1 1 303 951024060640060865139815 [(128,666543980414560246477920),(128,266657076463558573171808),(47,17823003761942045490087)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

theorem receipt_3_4 : Checked (bank 3 4) 4 1 1 := by
  refine checked_from_values (bank 3 4) 4 1 1
    (P3_7_1.checked (bank 3 4) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1387_302)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_3_4_2450_0 receipt_3_4_2450_1 receipt_3_4_2451_0 receipt_3_4_2451_1 (by decide +kernel) (by decide +kernel)

def group1_stage (i : Fin 4) : Fin 17 :=
  ⟨1+i.val, by have := i.isLt; omega⟩

theorem group1_checked (rect : Fin 4) (i : Fin 4) :
    Checked (bank rect (group1_stage i)) (reserve (group1_stage i))
      (excess rect) (seed rect) := by
  fin_cases i
  · fin_cases rect
    · exact receipt_0_1
    · exact receipt_1_1
    · exact receipt_2_1
    · exact receipt_3_1
  · fin_cases rect
    · exact receipt_0_2
    · exact receipt_1_2
    · exact receipt_2_2
    · exact receipt_3_2
  · fin_cases rect
    · exact receipt_0_3
    · exact receipt_1_3
    · exact receipt_2_3
    · exact receipt_3_3
  · fin_cases rect
    · exact receipt_0_4
    · exact receipt_1_4
    · exact receipt_2_4
    · exact receipt_3_4

end Lower6961.Hi.RescueSource
