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

theorem moment_2091_456 : momentEstimate 2091 456 = 528831085877 := mkM 2091 456 528831085877 [(128,713999520),(128,4660499616),(128,11781039264),(128,21223686286),(128,30814903104),(128,38594403136),(128,44457106240),(128,48403012416),(128,50432121664),(128,50544433984),(128,48739949376),(128,45018667840),(128,39383175281),(128,32263153930),(128,24796295029),(128,17602076717),(128,11142425823),(128,5851247200),(128,2140420704),(115,268468747)] rfl rfl (by dsimp only [mblk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

theorem moment_2100_439 : momentEstimate 2100 439 = 520524444033 := mkM 2100 439 520524444033 [(128,717219360),(128,4682741280),(128,11841177120),(128,21283064550),(128,30575072000),(128,38068785920),(128,43717006080),(128,47519732480),(128,49476965120),(128,49588704000),(128,47854949120),(128,44275700480),(128,38850961755),(128,31839629831),(128,24393218274),(128,17228999980),(128,10819779729),(128,5596600704),(128,1975910784),(107,218225466)] rfl rfl (by dsimp only [mblk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

theorem moment_2678_563 : momentEstimate 2678 563 = 1381475727537 := mkM 2678 563 1381475727537 [(128,924004640),(128,6111150368),(128,15703363872),(128,28895338784),(128,44725223347),(128,60197172864),(128,73351132800),(128,84139505280),(128,92562290304),(128,98619487872),(128,102311097984),(128,103637120640),(128,102597555840),(128,99192403584),(128,93421663872),(128,85285336704),(128,74814810745),(128,62882490764),(128,50739802930),(128,38959239188),(128,28030913412),(128,18344851056),(128,10401395312),(128,4554763888),(128,1056615024),(41,16996463)] rfl rfl (by dsimp only [mblk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

theorem moment_2678_584 : momentEstimate 2678 584 = 1421525065183 := mkM 2678 584 1421525065183 [(128,924004640),(128,6111150368),(128,15703363872),(128,28895338784),(128,44821712586),(128,60886126080),(128,74630499840),(128,85921205760),(128,94758243840),(128,101141614080),(128,105071316480),(128,106547351040),(128,105569717760),(128,102138416640),(128,96253447680),(128,87914810880),(128,77197419775),(128,65154508826),(128,52886238116),(128,40935577062),(128,29789439866),(128,19830964336),(128,11567529072),(128,5359630448),(128,1458926704),(62,56510648)] rfl rfl (by dsimp only [mblk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

theorem moment_2726_570 : momentEstimate 2726 570 = 1476869586813 := mkM 2726 570 1476869586813 [(128,941177120),(128,6229772576),(128,16024099104),(128,29518850336),(128,45788465784),(128,61910907968),(128,75709922368),(128,87113989184),(128,96123108416),(128,102737280064),(128,106956504128),(128,108780780608),(128,108210109504),(128,105244490816),(128,99883924544),(128,92128410688),(128,81979099023),(128,69908824467),(128,57337933609),(128,44969478669),(128,33309949796),(128,22790468361),(128,13842204672),(128,6924756992),(128,2297989120),(96,207088896)] rfl rfl (by dsimp only [mblk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

theorem moment_3438_750 : momentEstimate 3438 750 = 3859704881140 := mkM 3438 750 3859704881140 [(128,1195902240),(128,7989335328),(128,20781671712),(128,38767605024),(128,61141828896),(128,87096444885),(128,114498877888),(128,139366037952),(128,161083275712),(128,179650591168),(128,195067984320),(128,207335455168),(128,216453003712),(128,222420629952),(128,225238333888),(128,224906115520),(128,221423974848),(128,214791911872),(128,205009926592),(128,192078019008),(128,175996189120),(128,157132247091),(128,137136148062),(128,116886978890),(128,96919956452),(128,77735984777),(128,59798769904),(128,43425779232),(128,29202290208),(128,17520614944),(128,8632411680),(128,2789338656),(92,231246439)] rfl rfl (by dsimp only [mblk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem receipt_0_8_2450_0 : fastPhase (bank 0 8).shape 179818 2450 16 1 0 1 0 = 158221848420243249888328802 := mkP 0 8 2450 16 1 0 1 0 564 158221848420243249888328802 [(128,67668553158705340460481792),(128,47281036302754475934997760),(128,29108296895949772841614592),(128,13018922624967784110687648),(52,1145039437865876540547010)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem receipt_0_8_2450_1 : fastPhase (bank 0 8).shape 179818 2450 16 1 0 1 1 = 157613375592519714240815583 := mkP 0 8 2450 16 1 0 1 1 564 157613375592519714240815583 [(128,67502492684309990809001472),(128,47132195284687409540808192),(128,28975675993074643385556480),(128,12901534245989536505793814),(52,1101477384458133999655625)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem receipt_0_8_2451_0 : fastPhase (bank 0 8).shape 179818 2451 16 1 0 1 0 = 158223036371886399658800150 := mkP 0 8 2451 16 1 0 1 0 564 158223036371886399658800150 [(128,67669139178825185760807552),(128,47281389602840788142705280),(128,29108477576635508220168832),(128,13018986229645164625967421),(52,1145043783939752909151065)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem receipt_0_8_2451_1 : fastPhase (bank 0 8).shape 179818 2451 16 1 0 1 1 = 157614560009508132687630200 := mkP 0 8 2451 16 1 0 1 1 564 157614560009508132687630200 [(128,67503077516197563796934784),(128,47132547639780759712731264),(128,28975855950808394986115200),(128,12901597330165382116268052),(52,1101481572556032075580900)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

theorem receipt_0_8 : Checked (bank 0 8) 16 0 1 := by
  refine checked_from_values (bank 0 8) 16 0 1
    (P3_7_1.checked (bank 0 8) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_2678_563)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_0_8_2450_0 receipt_0_8_2450_1 receipt_0_8_2451_0 receipt_0_8_2451_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_1_8_2450_0 : fastPhase (bank 1 8).shape 179818 2450 16 1 0 2 0 = 141743323525023455859627027 := mkP 1 8 2450 16 1 0 2 0 564 141743323525023455859627027 [(128,60832213184024120811330144),(128,42346645304745227214703200),(128,25973960435205862851967584),(128,11575268640242123513543323),(52,1015235960806121468082776)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem receipt_1_8_2450_1 : fastPhase (bank 1 8).shape 179818 2450 16 1 0 2 1 = 141195338430990695455701631 := mkP 1 8 2450 16 1 0 2 1 564 141195338430990695455701631 [(128,60681167897127393832806624),(128,42212111538441584490354912),(128,25854874862552830501193952),(128,11470591424031844625548483),(52,976592708837042005797660)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem receipt_1_8_2451_0 : fastPhase (bank 1 8).shape 179818 2451 16 1 0 2 0 = 141744388453720084400198890 := mkP 1 8 2451 16 1 0 2 0 564 141744388453720084400198890 [(128,60832740022123067900447104),(128,42346961749620155315030400),(128,25974121671082721618217344),(128,11575325196636990456555915),(52,1015239814257149109948127)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem receipt_1_8_2451_1 : fastPhase (bank 1 8).shape 179818 2451 16 1 0 2 1 = 141196400166342671182401110 := mkP 1 8 2451 16 1 0 2 1 564 141196400166342671182401110 [(128,60681693651726945781575232),(128,42212427127729470756851264),(128,25855035448648146191035968),(128,11470647516095693555034436),(52,976596422142414897904210)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

theorem receipt_1_8 : Checked (bank 1 8) 16 0 2 := by
  refine checked_from_values (bank 1 8) 16 0 2
    (P3_7_1.checked (bank 1 8) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_2678_563)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_1_8_2450_0 receipt_1_8_2450_1 receipt_1_8_2451_0 receipt_1_8_2451_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_2_8_2450_0 : fastPhase (bank 2 8).shape 179818 2450 16 1 0 7 0 = 73964440100184021127690542 := mkP 2 8 2450 16 1 0 7 0 564 73964440100184021127690542 [(128,32547257012654595450748704),(128,22054133891188821126262560),(128,13162766088826286420860704),(128,5709949444610584428701178),(52,490333662903733701117396)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem receipt_2_8_2450_1 : fastPhase (bank 2 8).shape 179818 2450 16 1 0 7 1 = 73667452294011330926682651 := mkP 2 8 2450 16 1 0 7 1 564 73667452294011330926682651 [(128,32459661110473830098931744),(128,21979401967711561015951392),(128,13099615018677240181288992),(128,5657175989351171725428288),(52,471598207797527905082235)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem receipt_2_8_2451_0 : fastPhase (bank 2 8).shape 179818 2451 16 1 0 7 0 = 73964998452782803934011740 := mkP 2 8 2451 16 1 0 7 0 564 73964998452782803934011740 [(128,32547538972239891524222464),(128,22054298757501892594204160),(128,13162847837854421987556864),(128,5709977360959772092300080),(52,490335524226825735728172)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem receipt_2_8_2451_1 : fastPhase (bank 2 8).shape 179818 2451 16 1 0 7 1 = 73668008877612957018269810 := mkP 2 8 2451 16 1 0 7 1 564 73668008877612957018269810 [(128,32459942431392639542769792),(128,21979566353352520162769024),(128,13099696420825617676810368),(128,5657203670896197694471566),(52,471600001145981941449060)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

theorem receipt_2_8 : Checked (bank 2 8) 16 0 7 := by
  refine checked_from_values (bank 2 8) 16 0 7
    (P3_7_1.checked (bank 2 8) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_2678_563)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_2_8_2450_0 receipt_2_8_2450_1 receipt_2_8_2451_0 receipt_2_8_2451_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_3_8_2450_0 : fastPhase (bank 3 8).shape 179818 2450 16 1 1 1 0 = 47522149181742430640412825 := mkP 3 8 2450 16 1 1 1 0 585 47522149181742430640412825 [(128,20010953400411843268481824),(128,14039814110772921925452576),(128,8739261828775527469937440),(128,4144113270497337150710560),(73,588006571284800825830425)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem receipt_3_8_2450_1 : fastPhase (bank 3 8).shape 179818 2450 16 1 1 1 1 = 47342456537923300649615850 := mkP 3 8 2450 16 1 1 1 1 585 47342456537923300649615850 [(128,19962416733780560078093600),(128,13996184551868622406372640),(128,8700843307627413668355360),(128,4111200541766091748699424),(73,571811402880612748094826)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem receipt_3_8_2451_0 : fastPhase (bank 3 8).shape 179818 2451 16 1 1 1 0 = 47522457829906539672141846 := mkP 3 8 2451 16 1 1 1 0 585 47522457829906539672141846 [(128,20011120022098789737546176),(128,14039903891251452276261312),(128,8739301570091438477066688),(128,4144124918956510106567104),(73,588007427508349074700566)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem receipt_3_8_2451_1 : fastPhase (bank 3 8).shape 179818 2451 16 1 1 1 1 = 47342764096862828973886728 := mkP 3 8 2451 16 1 1 1 1 585 47342764096862828973886728 [(128,19962582891660584294797184),(128,13996274017842957249867648),(128,8700882856632414944497536),(128,4111212093690399259176832),(73,571812237036473225547528)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

theorem receipt_3_8 : Checked (bank 3 8) 16 1 1 := by
  refine checked_from_values (bank 3 8) 16 1 1
    (P3_7_1.checked (bank 3 8) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_2678_584)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_3_8_2450_0 receipt_3_8_2450_1 receipt_3_8_2451_0 receipt_3_8_2451_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_0_9_2450_0 : fastPhase (bank 0 9).shape 179818 2450 10 1 0 1 0 = 35036298901616009363115918 := mkP 0 9 2450 10 1 0 1 0 440 35036298901616009363115918 [(128,18366024920867510128851683),(128,11181544121617266771710128),(128,5002980551181426022098028),(56,485749307949806440456079)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem receipt_0_9_2450_1 : fastPhase (bank 0 9).shape 179818 2450 10 1 0 1 1 = 34863693696384101149058348 := mkP 0 9 2450 10 1 0 1 1 440 34863693696384101149058348 [(128,18306544256253421841853799),(128,11129952386659366019003545),(128,4958683592036618738988171),(56,468513461434694549212833)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem receipt_0_9_2451_0 : fastPhase (bank 0 9).shape 179818 2451 10 1 0 1 0 = 35036565210457644296504783 := mkP 0 9 2451 10 1 0 1 0 440 35036565210457644296504783 [(128,18366183385635899996573286),(128,11181623042513463422820641),(128,5003007529198546417606573),(56,485751253109734459504283)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem receipt_0_9_2451_1 : fastPhase (bank 0 9).shape 179818 2451 10 1 0 1 1 = 34863958989682240929577520 := mkP 0 9 2451 10 1 0 1 1 440 34863958989682240929577520 [(128,18306702295869786957842508),(128,11130030994938227162100034),(128,4958710357283210456164315),(56,468515341591016353470663)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

theorem receipt_0_9 : Checked (bank 0 9) 10 0 1 := by
  refine checked_from_values (bank 0 9) 10 0 1
    (P3_7_1.checked (bank 0 9) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_2100_439)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_0_9_2450_0 receipt_0_9_2450_1 receipt_0_9_2451_0 receipt_0_9_2451_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_1_9_2450_0 : fastPhase (bank 1 9).shape 179818 2450 10 1 0 2 0 = 31433581953221571189064605 := mkP 1 9 2450 10 1 0 2 0 440 31433581953221571189064605 [(128,16527807777818561325595251),(128,10014408110463134435476578),(128,4459917647829629498494242),(56,431448417110245929498534)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem receipt_1_9_2450_1 : fastPhase (bank 1 9).shape 179818 2450 10 1 0 2 1 = 31277898973059105334843089 := mkP 1 9 2450 10 1 0 2 1 440 31277898973059105334843089 [(128,16473663998474264052210303),(128,9967830781118239545600996),(128,4420275606918715640793666),(56,416128586547886096238124)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem receipt_1_9_2451_0 : fastPhase (bank 1 9).shape 179818 2451 10 1 0 2 0 = 31433821037567173108779762 := mkP 1 9 2451 10 1 0 2 0 440 31433821037567173108779762 [(128,16527950392087848156163047),(128,10014478800182562866923588),(128,4459941700427469893545634),(56,431450144869292192147493)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem receipt_1_9_2451_1 : fastPhase (bank 1 9).shape 179818 2451 10 1 0 2 1 = 31278137138501111198545686 := mkP 1 9 2451 10 1 0 2 1 440 31278137138501111198545686 [(128,16473806224792182939530125),(128,9967901188202567994593568),(128,4420299468982607346288353),(56,416130256523752918133640)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

theorem receipt_1_9 : Checked (bank 1 9) 10 0 2 := by
  refine checked_from_values (bank 1 9) 10 0 2
    (P3_7_1.checked (bank 1 9) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_2100_439)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_1_9_2450_0 receipt_1_9_2450_1 receipt_1_9_2451_0 receipt_1_9_2451_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_2_9_2450_0 : fastPhase (bank 2 9).shape 179818 2450 10 1 0 7 0 = 16577108912105295266177206 := mkP 2 9 2450 10 1 0 7 0 440 16577108912105295266177206 [(128,8908337893540461097657519),(128,5214081098418439531620510),(128,2243514955700118730202402),(56,211174964446275906696775)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem receipt_2_9_2450_1 : fastPhase (bank 2 9).shape 179818 2450 10 1 0 7 1 = 16491828348980597258462488 := mkP 2 9 2450 10 1 0 7 1 440 16491828348980597258462488 [(128,8876774081132113976251367),(128,5188419368632580729431453),(128,2222998148014249569536495),(56,203636751201652983243173)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem receipt_2_9_2451_0 : fastPhase (bank 2 9).shape 179818 2451 10 1 0 7 0 = 16577235604962713436462897 := mkP 2 9 2451 10 1 0 7 0 440 16577235604962713436462897 [(128,8908414799591392358953958),(128,5214117928803667770077171),(128,2243527066294984892737183),(56,211175810272668414694585)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem receipt_2_9_2451_1 : fastPhase (bank 2 9).shape 179818 2451 10 1 0 7 1 = 16491954527295772457539108 := mkP 2 9 2451 10 1 0 7 1 440 16491954527295772457539108 [(128,8876850757403835526122996),(128,5188456041777821593690822),(128,2223010159539644191147489),(56,203637568574471146577801)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

theorem receipt_2_9 : Checked (bank 2 9) 10 0 7 := by
  refine checked_from_values (bank 2 9) 10 0 7
    (P3_7_1.checked (bank 2 9) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_2100_439)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_2_9_2450_0 receipt_2_9_2450_1 receipt_2_9_2451_0 receipt_2_9_2451_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_3_9_2450_0 : fastPhase (bank 3 9).shape 179818 2450 10 1 1 1 0 = 10613780318826716899759324 := mkP 3 9 2450 10 1 1 1 0 457 10613780318826716899759324 [(128,5475235589701358924035872),(128,3358330920052438558099232),(128,1562726905639148150462240),(73,217486903433771267161980)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem receipt_3_9_2450_1 : fastPhase (bank 3 9).shape 179818 2450 10 1 1 1 1 = 10562426131493615985521762 := mkP 3 9 2450 10 1 1 1 1 457 10562426131493615985521762 [(128,5457722678601245515983520),(128,3343159558249443962174112),(128,1550076468262202390039200),(73,211467426380724117324930)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem receipt_3_9_2451_0 : fastPhase (bank 3 9).shape 179818 2451 10 1 1 1 0 = 10613849633476068780669272 := mkP 3 9 2451 10 1 1 1 0 457 10613849633476068780669272 [(128,5475280068429449591699328),(128,3358350032832024322004864),(128,1562732264131285272885120),(73,217487268083309594079960)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem receipt_3_9_2451_1 : fastPhase (bank 3 9).shape 179818 2451 10 1 1 1 1 = 10562495132920240544993840 := mkP 3 9 2451 10 1 1 1 1 457 10562495132920240544993840 [(128,5457766994929237847183360),(128,3343178575116118062919680),(128,1550081781233252720431104),(73,211467781641631914459696)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

theorem receipt_3_9 : Checked (bank 3 9) 10 1 1 := by
  refine checked_from_values (bank 3 9) 10 1 1
    (P3_7_1.checked (bank 3 9) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_2091_456)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_3_9_2450_0 receipt_3_9_2450_1 receipt_3_9_2451_0 receipt_3_9_2451_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_0_10_2450_0 : fastPhase (bank 0 10).shape 179818 2450 20 1 0 1 0 = 692569779070634300883364794 := mkP 0 10 2450 20 1 0 1 0 751 692569779070634300883364794 [(128,231937462176173454552926592),(128,179636593666974704737610112),(128,131745909069982699284449664),(128,88063582143581371090151808),(128,48389755063007131500107547),(111,12796476950914939718119071)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem receipt_0_10_2450_1 : fastPhase (bank 0 10).shape 179818 2450 20 1 0 1 1 = 690561034626109583538688656 := mkP 0 10 2450 20 1 0 1 1 751 690561034626109583538688656 [(128,231516972514051169537539584),(128,179250167618622684861439488),(128,131392013574864187779939840),(128,87740698853971553558257152),(128,48096380018742293573270853),(111,12564802045857694228241739)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem receipt_0_10_2451_0 : fastPhase (bank 0 10).shape 179818 2451 20 1 0 1 0 = 692574982528235685830848598 := mkP 0 10 2451 20 1 0 1 0 751 692574982528235685830848598 [(128,231939514010867605796103488),(128,179638018282814151159645504),(128,131746826584269867247265088),(128,88064105869729803594024256),(128,48389991123660946589639400),(111,12796526656893311444170862)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem receipt_0_10_2451_1 : fastPhase (bank 0 10).shape 179818 2451 20 1 0 1 1 = 690566226540756538414619132 := mkP 0 10 2451 20 1 0 1 1 751 690566226540756538414619132 [(128,231519021302858369202082688),(128,179251589672656465846178688),(128,131392928978910225734816640),(128,87741220889292779754230656),(128,48096614779146270263576096),(111,12564850917892427613734364)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

theorem receipt_0_10 : Checked (bank 0 10) 20 0 1 := by
  refine checked_from_values (bank 0 10) 20 0 1
    (P3_7_1.checked (bank 0 10) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_3438_750)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_0_10_2450_0 receipt_0_10_2450_1 receipt_0_10_2451_0 receipt_0_10_2451_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_1_10_2450_0 : fastPhase (bank 1 10).shape 179818 2450 20 1 0 2 0 = 614768526425386334702848632 := mkP 1 10 2450 20 1 0 2 0 751 614768526425386334702848632 [(128,206756612410848886892171808),(128,159645899453190071842021920),(128,116727101895395781252657696),(128,77786322345698987579851296),(128,42613518246073020492444030),(111,11239072074179586643701882)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem receipt_1_10_2450_1 : fastPhase (bank 1 10).shape 179818 2450 20 1 0 2 1 = 612975166162593758483483652 := mkP 1 10 2450 20 1 0 2 1 751 612975166162593758483483652 [(128,206376860160076039017218976),(128,159298672864700533038093216),(128,116410766796481493320000416),(128,77499273760798841351844768),(128,42354179959290135387243828),(111,11035412621246716369082448)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem receipt_1_10_2451_0 : fastPhase (bank 1 10).shape 179818 2451 20 1 0 2 0 = 614773148790089637060843995 := mkP 1 10 2451 20 1 0 2 0 751 614773148790089637060843995 [(128,206758441530094791216255552),(128,159647165570357989899432512),(128,116727914844355010919076416),(128,77786784972459097853473344),(128,42613726140408620319779920),(111,11239115732414126852826251)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem receipt_1_10_2451_1 : fastPhase (bank 1 10).shape 179818 2451 20 1 0 2 1 = 612979778184718567867760599 := mkP 1 10 2451 20 1 0 2 1 751 612979778184718567867760599 [(128,206378686520553223067767040),(128,159299936674897775753695488),(128,116411577856297271994650880),(128,77499734882993217852739840),(128,42354386703709260906696369),(111,11035455546267818292210982)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

theorem receipt_1_10 : Checked (bank 1 10) 20 0 2 := by
  refine checked_from_values (bank 1 10) 20 0 2
    (P3_7_1.checked (bank 1 10) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_3438_750)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_1_10_2450_0 receipt_1_10_2450_1 receipt_1_10_2451_0 receipt_1_10_2451_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_2_10_2450_0 : fastPhase (bank 2 10).shape 179818 2450 20 1 0 7 0 = 300597346858727189825080754 := mkP 2 10 2450 20 1 0 7 0 751 300597346858727189825080754 [(128,104334922783088634413504928),(128,78741536710419812749724064),(128,56252498772058847200983456),(128,36615834954476870584281504),(128,19592370858390063682599639),(111,5060182780292961193987163)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem receipt_2_10_2450_1 : fastPhase (bank 2 10).shape 179818 2450 20 1 0 7 1 = 299682219566915639387987243 := mkP 2 10 2450 20 1 0 7 1 751 299682219566915639387987243 [(128,104124844693056858337650336),(128,78556139259210457554507424),(128,56089812507681663266293408),(128,36473989182339224228116128),(128,19469591163259578454090550),(111,4967842761367857547329397)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem receipt_2_10_2451_0 : fastPhase (bank 2 10).shape 179818 2451 20 1 0 7 0 = 300599619698001048098502226 := mkP 2 10 2451 20 1 0 7 0 751 300599619698001048098502226 [(128,104335845981777121238725312),(128,78742161335247197038940864),(128,56252890653401158679327424),(128,36616052799693495426765504),(128,19592466485001836965016385),(111,5060202442880238749726737)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem receipt_2_10_2451_1 : fastPhase (bank 2 10).shape 179818 2451 20 1 0 7 1 = 299684486990488648906435411 := mkP 2 10 2451 20 1 0 7 1 751 299684486990488648906435411 [(128,104125766336054753568182016),(128,78556762633728202551545600),(128,56090203406985214506520320),(128,36474206279024792007036672),(128,19469686243593388095209134),(111,4967862091102298177941669)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

theorem receipt_2_10 : Checked (bank 2 10) 20 0 7 := by
  refine checked_from_values (bank 2 10) 20 0 7
    (P3_7_1.checked (bank 2 10) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_3438_750)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_2_10_2450_0 receipt_2_10_2450_1 receipt_2_10_2451_0 receipt_2_10_2451_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_3_10_2450_0 : fastPhase (bank 3 10).shape 179818 2450 20 1 1 1 0 = 60145854795848467541915019 := mkP 3 10 2450 20 1 1 1 0 571 60145854795848467541915019 [(128,25725796227884936436628320),(128,17935561691044653744434016),(128,11000484668291546162240352),(128,4966639008357609566669664),(59,517373200269721631942667)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem receipt_3_10_2450_1 : fastPhase (bank 3 10).shape 179818 2450 20 1 1 1 1 = 59914373373091666690638399 := mkP 3 10 2450 20 1 1 1 1 571 59914373373091666690638399 [(128,25662529038426921073318752),(128,17878543882329882469018464),(128,10950116007105527707810656),(128,4923308830504527521336160),(59,499875614724807919154367)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem receipt_3_10_2451_0 : fastPhase (bank 3 10).shape 179818 2451 20 1 1 1 0 = 60146248534790584517047697 := mkP 3 10 2451 20 1 1 1 0 571 60146248534790584517047697 [(128,25726009881667818571354016),(128,17935676421910529733132192),(128,11000534971764011948322720),(128,4966653245557662338965408),(59,517374013890561925273361)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem receipt_3_10_2451_1 : fastPhase (bank 3 10).shape 179818 2451 20 1 1 1 1 = 59914765695210860704076741 := mkP 3 10 2451 20 1 1 1 1 571 59914765695210860704076741 [(128,25662742091013246011454752),(128,17878658203681273327740192),(128,10950166058569516045341984),(128,4923322939805729271301408),(59,499876402141096048238405)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

theorem receipt_3_10 : Checked (bank 3 10) 20 1 1 := by
  refine checked_from_values (bank 3 10) 20 1 1
    (P3_7_1.checked (bank 3 10) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_2726_570)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_3_10_2450_0 receipt_3_10_2450_1 receipt_3_10_2451_0 receipt_3_10_2451_1 (by decide +kernel) (by decide +kernel)

def group3_stage (i : Fin 3) : Fin 17 :=
  ⟨8+i.val, by have := i.isLt; omega⟩

theorem group3_checked (rect : Fin 4) (i : Fin 3) :
    Checked (bank rect (group3_stage i)) (reserve (group3_stage i))
      (excess rect) (seed rect) := by
  fin_cases i
  · fin_cases rect
    · exact receipt_0_8
    · exact receipt_1_8
    · exact receipt_2_8
    · exact receipt_3_8
  · fin_cases rect
    · exact receipt_0_9
    · exact receipt_1_9
    · exact receipt_2_9
    · exact receipt_3_9
  · fin_cases rect
    · exact receipt_0_10
    · exact receipt_1_10
    · exact receipt_2_10
    · exact receipt_3_10

end Lower6961.Hi.RescueSource
