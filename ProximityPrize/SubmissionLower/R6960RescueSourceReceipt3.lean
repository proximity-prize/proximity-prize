import ProximityPrize.SubmissionLower.Z6970CompactRankBlocks
import ProximityPrize.SubmissionLower.R6960RescueSourceReceipt1

set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 18000

namespace Lower6960.RescueSource
open P1_7 (Bank debit)
open P1_7_1_3 (blockEstimate block_append momentEstimate)
open HelperSource (WidthGuard)

theorem moment_2091_456 : momentEstimate 2091 456 = 528831085877 :=
  CompactRank6970.from_blocks (f := P1_7_1_3.offsetEstimate 2091 456) (start := 456)
    [
      (128,713999520), (128,4660499616), (128,11781039264), (128,21223686286), (128,30814903104),
      (128,38594403136), (128,44457106240), (128,48403012416), (128,50432121664), (128,50544433984),
      (128,48739949376), (128,45018667840), (128,39383175281), (128,32263153930), (128,24796295029),
      (128,17602076717), (128,11142425823), (128,5851247200), (128,2140420704), (115,268468747)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel)

theorem moment_2100_439 : momentEstimate 2100 439 = 520524444033 :=
  CompactRank6970.from_blocks (f := P1_7_1_3.offsetEstimate 2100 439) (start := 439)
    [
      (128,717219360), (128,4682741280), (128,11841177120), (128,21283064550), (128,30575072000),
      (128,38068785920), (128,43717006080), (128,47519732480), (128,49476965120), (128,49588704000),
      (128,47854949120), (128,44275700480), (128,38850961755), (128,31839629831), (128,24393218274),
      (128,17228999980), (128,10819779729), (128,5596600704), (128,1975910784), (107,218225466)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel)

theorem moment_2678_563 : momentEstimate 2678 563 = 1381475727537 :=
  CompactRank6970.from_blocks (f := P1_7_1_3.offsetEstimate 2678 563) (start := 563)
    [
      (128,924004640), (128,6111150368), (128,15703363872), (128,28895338784), (128,44725223347),
      (128,60197172864), (128,73351132800), (128,84139505280), (128,92562290304), (128,98619487872),
      (128,102311097984), (128,103637120640), (128,102597555840), (128,99192403584),
      (128,93421663872), (128,85285336704), (128,74814810745), (128,62882490764), (128,50739802930),
      (128,38959239188), (128,28030913412), (128,18344851056), (128,10401395312), (128,4554763888),
      (128,1056615024), (41,16996463)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel)

theorem moment_2678_584 : momentEstimate 2678 584 = 1421525065183 :=
  CompactRank6970.from_blocks (f := P1_7_1_3.offsetEstimate 2678 584) (start := 584)
    [
      (128,924004640), (128,6111150368), (128,15703363872), (128,28895338784), (128,44821712586),
      (128,60886126080), (128,74630499840), (128,85921205760), (128,94758243840),
      (128,101141614080), (128,105071316480), (128,106547351040), (128,105569717760),
      (128,102138416640), (128,96253447680), (128,87914810880), (128,77197419775),
      (128,65154508826), (128,52886238116), (128,40935577062), (128,29789439866), (128,19830964336),
      (128,11567529072), (128,5359630448), (128,1458926704), (62,56510648)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel)

theorem moment_2726_570 : momentEstimate 2726 570 = 1476869586813 :=
  CompactRank6970.from_blocks (f := P1_7_1_3.offsetEstimate 2726 570) (start := 570)
    [
      (128,941177120), (128,6229772576), (128,16024099104), (128,29518850336), (128,45788465784),
      (128,61910907968), (128,75709922368), (128,87113989184), (128,96123108416),
      (128,102737280064), (128,106956504128), (128,108780780608), (128,108210109504),
      (128,105244490816), (128,99883924544), (128,92128410688), (128,81979099023),
      (128,69908824467), (128,57337933609), (128,44969478669), (128,33309949796), (128,22790468361),
      (128,13842204672), (128,6924756992), (128,2297989120), (96,207088896)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel)

theorem moment_3438_750 : momentEstimate 3438 750 = 3859704881140 :=
  CompactRank6970.from_blocks (f := P1_7_1_3.offsetEstimate 3438 750) (start := 750)
    [
      (128,1195902240), (128,7989335328), (128,20781671712), (128,38767605024), (128,61141828896),
      (128,87096444885), (128,114498877888), (128,139366037952), (128,161083275712),
      (128,179650591168), (128,195067984320), (128,207335455168), (128,216453003712),
      (128,222420629952), (128,225238333888), (128,224906115520), (128,221423974848),
      (128,214791911872), (128,205009926592), (128,192078019008), (128,175996189120),
      (128,157132247091), (128,137136148062), (128,116886978890), (128,96919956452),
      (128,77735984777), (128,59798769904), (128,43425779232), (128,29202290208), (128,17520614944),
      (128,8632411680), (128,2789338656), (92,231246439)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel)

private theorem receipt_0_8_2359_0 : fastPhase (bank 0 8).shape 179818 2359 16 1 0 1 0 = 1232157488973810264378926772 :=
  phase_of_block (n := 564) (by decide +kernel)
    (CompactRank6970.from_blocks (f := fastLayer (bank 0 8).shape 179818 2359 16 1 0 1 0) (start := 0)
      [
      (128,525856775702927980658442368), (128,368253393045625592464703616),
      (128,227223763833173951540654584), (128,101850431499216355258641714),
      (52,8973124892866384456484490)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel))

private theorem receipt_0_8_2359_1 : fastPhase (bank 0 8).shape 179818 2359 16 1 0 1 1 = 1227432693126806080448810056 :=
  phase_of_block (n := 564) (by decide +kernel)
    (CompactRank6970.from_blocks (f := fastLayer (bank 0 8).shape 179818 2359 16 1 0 1 1) (start := 0)
      [
      (128,524574935357150421879720512), (128,367100157747075655619160640),
      (128,226192180387871483389814282), (128,100933576557325787331361738),
      (52,8631843077382732228752884)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel))

private theorem receipt_0_8_2360_0 : fastPhase (bank 0 8).shape 179818 2360 16 1 0 1 0 = 1232166742092095404938999713 :=
  phase_of_block (n := 564) (by decide +kernel)
    (CompactRank6970.from_blocks (f := fastLayer (bank 0 8).shape 179818 2360 16 1 0 1 0) (start := 0)
      [
      (128,525861333186702714169851168), (128,368256146551849968989334816),
      (128,227225174886282310245107012), (128,101850928556833924600259972),
      (52,8973158910426486934446745)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel))

private theorem receipt_0_8_2360_1 : fastPhase (bank 0 8).shape 179818 2360 16 1 0 1 1 = 1227441918843231792654734460 :=
  phase_of_block (n := 564) (by decide +kernel)
    (CompactRank6970.from_blocks (f := fastLayer (bank 0 8).shape 179818 2360 16 1 0 1 1) (start := 0)
      [
      (128,524579483676391155402499104), (128,367102903934346839803663392),
      (128,226193585818437530355965600), (128,100934069555133399009254536),
      (52,8631875858922868083351828)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel))

theorem receipt_0_8 : Checked (bank 0 8) 16 0 1 := by
  refine checked_from_values (bank 0 8) 16 0 1
    (P3_7_1.checked (bank 0 8) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_2678_563)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_0_8_2359_0 receipt_0_8_2359_1 receipt_0_8_2360_0 receipt_0_8_2360_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_1_8_2359_0 : fastPhase (bank 1 8).shape 179818 2359 16 1 0 2 0 = 1107094408873269185185810749 :=
  phase_of_block (n := 564) (by decide +kernel)
    (CompactRank6970.from_blocks (f := fastLayer (bank 1 8).shape 179818 2359 16 1 0 2 0) (start := 0)
      [
      (128,473072128141981128006662912), (128,330848373077588320295189248),
      (128,203873943919120236351359850), (128,91267165255744633758211614),
      (52,8032798478834866774387125)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel))

private theorem receipt_1_8_2359_1 : fastPhase (bank 1 8).shape 179818 2359 16 1 0 2 1 = 1102841140258512452297258320 :=
  phase_of_block (n := 564) (by decide +kernel)
    (CompactRank6970.from_blocks (f := fastLayer (bank 1 8).shape 179818 2359 16 1 0 2 1) (start := 0)
      [
      (128,471914048414699092027261632), (128,329808855032575781982642880),
      (128,202946285632585196129001903), (128,90444724844514073815098049),
      (52,7727226334138308343253856)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel))

private theorem receipt_1_8_2360_0 : fastPhase (bank 1 8).shape 179818 2360 16 1 0 2 0 = 1107102724767319488862970598 :=
  phase_of_block (n := 564) (by decide +kernel)
    (CompactRank6970.from_blocks (f := fastLayer (bank 1 8).shape 179818 2360 16 1 0 2 0) (start := 0)
      [
      (128,473076228213627952283337792), (128,330850846944198022767617088),
      (128,203875210000253249121977922), (128,91267610677515072302264457),
      (52,8032828931725192387773339)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel))

private theorem receipt_1_8_2360_1 : fastPhase (bank 1 8).shape 179818 2360 16 1 0 2 1 = 1102849431457158291868243023 :=
  phase_of_block (n := 564) (by decide +kernel)
    (CompactRank6970.from_blocks (f := fastLayer (bank 1 8).shape 179818 2360 16 1 0 2 1) (start := 0)
      [
      (128,471918140199035059135567680), (128,329811322297915480118359872),
      (128,202947546655885531321967343), (128,90445166624004931903976928),
      (52,7727255680317289388371200)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel))

theorem receipt_1_8 : Checked (bank 1 8) 16 0 2 := by
  refine checked_from_values (bank 1 8) 16 0 2
    (P3_7_1.checked (bank 1 8) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_2678_563)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_1_8_2359_0 receipt_1_8_2359_1 receipt_1_8_2360_0 receipt_1_8_2360_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_2_8_2359_0 : fastPhase (bank 2 8).shape 179818 2359 16 1 0 7 0 = 585034184204402944456480281 :=
  phase_of_block (n := 564) (by decide +kernel)
    (CompactRank6970.from_blocks (f := fastLayer (bank 2 8).shape 179818 2359 16 1 0 7 0) (start := 0)
      [
      (128,252248805222111223602157952), (128,174723741147929117675641216),
      (128,106636865228084883583381488), (128,47292447523525475562375195),
      (52,4132325082752244032924430)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel))

private theorem receipt_2_8_2359_1 : fastPhase (bank 2 8).shape 179818 2359 16 1 0 7 1 = 582755732474326911158434477 :=
  phase_of_block (n := 564) (by decide +kernel)
    (CompactRank6970.from_blocks (f := fastLayer (bank 2 8).shape 179818 2359 16 1 0 7 1) (start := 0)
      [
      (128,251612418778540322186416320), (128,174161655228466152920854720),
      (128,106143708852357176297520093), (128,46863026934371414324737593),
      (52,3974922680591845428905751)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel))

private theorem receipt_2_8_2360_0 : fastPhase (bank 2 8).shape 179818 2360 16 1 0 7 0 = 585038586162608078110730745 :=
  phase_of_block (n := 564) (by decide +kernel)
    (CompactRank6970.from_blocks (f := fastLayer (bank 2 8).shape 179818 2360 16 1 0 7 0) (start := 0)
      [
      (128,252250991672185665821937792), (128,174725047791091567962615936),
      (128,106637527568990491290828240), (128,47292678381076318356173565),
      (52,4132340749264034679175212)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel))

private theorem receipt_2_8_2360_1 : fastPhase (bank 2 8).shape 179818 2360 16 1 0 7 1 = 582760121095273397318020224 :=
  phase_of_block (n := 564) (by decide +kernel)
    (CompactRank6970.from_blocks (f := fastLayer (bank 2 8).shape 179818 2360 16 1 0 7 1) (start := 0)
      [
      (128,251614600645441716246883968), (128,174162958286855132575862400),
      (128,106144368497879443720642389), (128,46863255888148158343263846),
      (52,3974937776948946431367621)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel))

theorem receipt_2_8 : Checked (bank 2 8) 16 0 7 := by
  refine checked_from_values (bank 2 8) 16 0 7
    (P3_7_1.checked (bank 2 8) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_2678_563)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_2_8_2359_0 receipt_2_8_2359_1 receipt_2_8_2360_0 receipt_2_8_2360_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_3_8_2359_0 : fastPhase (bank 3 8).shape 179818 2359 16 1 1 1 0 = 109201000752084963409598586 :=
  phase_of_block (n := 585) (by decide +kernel)
    (CompactRank6970.from_blocks (f := fastLayer (bank 3 8).shape 179818 2359 16 1 1 1 0) (start := 0)
      [
      (128,45880589008074990286834176), (128,32264358998452178889861632),
      (128,20129467981124712353450496), (128,9566711755115393475455488),
      (73,1359873009317688403996794)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel))

private theorem receipt_3_8_2359_1 : fastPhase (bank 3 8).shape 179818 2359 16 1 1 1 1 = 108789344370429278708276124 :=
  phase_of_block (n := 585) (by decide +kernel)
    (CompactRank6970.from_blocks (f := fastLayer (bank 3 8).shape 179818 2359 16 1 1 1 1) (start := 0)
      [
      (128,45770078020298345583701952), (128,32164637881542881484435392),
      (128,20041312263347883969572800), (128,9490882652408121693269952),
      (73,1322433552832045977296028)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel))

private theorem receipt_3_8_2360_0 : fastPhase (bank 3 8).shape 179818 2360 16 1 1 1 0 = 109201709925801261665163657 :=
  phase_of_block (n := 585) (by decide +kernel)
    (CompactRank6970.from_blocks (f := fastLayer (bank 3 8).shape 179818 2360 16 1 1 1 0) (start := 0)
      [
      (128,45880971307479554555586720), (128,32264565428760563488495776),
      (128,20129559550178457575229600), (128,9566738649721182909003936),
      (73,1359874989661503136847625)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel))

private theorem receipt_3_8_2360_1 : fastPhase (bank 3 8).shape 179818 2360 16 1 1 1 1 = 108790051051514190578092002 :=
  phase_of_block (n := 585) (by decide +kernel)
    (CompactRank6970.from_blocks (f := fastLayer (bank 3 8).shape 179818 2360 16 1 1 1 1) (start := 0)
      [
      (128,45770459261866048688115360), (128,32164843592137408062496416),
      (128,20041403390798886315224736), (128,9490909324551232401620640),
      (73,1322435482160615110634850)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel))

theorem receipt_3_8 : Checked (bank 3 8) 16 1 1 := by
  refine checked_from_values (bank 3 8) 16 1 1
    (P3_7_1.checked (bank 3 8) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_2678_584)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_3_8_2359_0 receipt_3_8_2359_1 receipt_3_8_2360_0 receipt_3_8_2360_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_0_9_2359_0 : fastPhase (bank 0 9).shape 179818 2359 10 1 0 1 0 = 259707070416901245955592262 :=
  phase_of_block (n := 440) (by decide +kernel)
    (CompactRank6970.from_blocks (f := fastLayer (bank 0 9).shape 179818 2359 10 1 0 1 0) (start := 0)
      [
      (128,135888818933834375379608720), (128,82968921164467395215175926),
      (128,37226980351255568178627248), (56,3622349967343907182180368)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel))

private theorem receipt_0_9_2359_1 : fastPhase (bank 0 9).shape 179818 2359 10 1 0 1 1 = 258431315290432078243089352 :=
  phase_of_block (n := 440) (by decide +kernel)
    (CompactRank6970.from_blocks (f := fastLayer (bank 0 9).shape 179818 2359 10 1 0 1 1) (start := 0)
      [
      (128,135451559110264090631330102), (128,82587813663086087687053680),
      (128,36898076208333671486061486), (56,3493866308748228438644084)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel))

private theorem receipt_0_9_2360_0 : fastPhase (bank 0 9).shape 179818 2360 10 1 0 1 0 = 259709043213596586942148409 :=
  phase_of_block (n := 440) (by decide +kernel)
    (CompactRank6970.from_blocks (f := fastLayer (bank 0 9).shape 179818 2360 10 1 0 1 0) (start := 0)
      [
      (128,135889991580852729540995198), (128,82969506290070519966201110),
      (128,37227180887027749862499925), (56,3622364455645587572452176)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel))

private theorem receipt_0_9_2360_1 : fastPhase (bank 0 9).shape 179818 2360 10 1 0 1 1 = 258433280599274765119960845 :=
  phase_of_block (n := 440) (by decide +kernel)
    (CompactRank6970.from_blocks (f := fastLayer (bank 0 9).shape 179818 2360 10 1 0 1 1) (start := 0)
      [
      (128,135452728636306989341986356), (128,82588396483315436656235799),
      (128,36898275166535450613030948), (56,3493880313116888508707742)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel))

theorem receipt_0_9 : Checked (bank 0 9) 10 0 1 := by
  refine checked_from_values (bank 0 9) 10 0 1
    (P3_7_1.checked (bank 0 9) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_2100_439)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_0_9_2359_0 receipt_0_9_2359_1 receipt_0_9_2360_0 receipt_0_9_2360_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_1_9_2359_0 : fastPhase (bank 1 9).shape 179818 2359 10 1 0 2 0 = 233701338827268645797806012 :=
  phase_of_block (n := 440) (by decide +kernel)
    (CompactRank6970.from_blocks (f := fastLayer (bank 1 9).shape 179818 2359 10 1 0 2 0) (start := 0)
      [
      (128,122418681222027075490320887), (128,74613718261226252948101185),
      (128,33421208087350652022092766), (56,3247731256664665337291174)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel))

private theorem receipt_1_9_2359_1 : fastPhase (bank 1 9).shape 179818 2359 10 1 0 2 1 = 232551084270889353868783426 :=
  phase_of_block (n := 440) (by decide +kernel)
    (CompactRank6970.from_blocks (f := fastLayer (bank 1 9).shape 179818 2359 10 1 0 2 1) (start := 0)
      [
      (128,122023089136617515283369738), (128,74269979482447551895541892),
      (128,33125509782627091771359333), (56,3132505869197194918512463)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel))

private theorem receipt_1_9_2360_0 : fastPhase (bank 1 9).shape 179818 2360 10 1 0 2 0 = 233703114514376763274911400 :=
  phase_of_block (n := 440) (by decide +kernel)
    (CompactRank6970.from_blocks (f := fastLayer (bank 1 9).shape 179818 2360 10 1 0 2 0) (start := 0)
      [
      (128,122419737656342541397331338), (128,74614244481117084399425078),
      (128,33421388130190478109083711), (56,3247744246726659369071273)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel))

private theorem receipt_1_9_2360_1 : fastPhase (bank 1 9).shape 179818 2360 10 1 0 2 1 = 232552853198765527313763753 :=
  phase_of_block (n := 440) (by decide +kernel)
    (CompactRank6970.from_blocks (f := fastLayer (bank 1 9).shape 179818 2360 10 1 0 2 1) (start := 0)
      [
      (128,122024142744771976905029646), (128,74270503621913257875844281),
      (128,33125688406832419950141277), (56,3132518425247872582748549)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel))

theorem receipt_1_9 : Checked (bank 1 9) 10 0 2 := by
  refine checked_from_values (bank 1 9) 10 0 2
    (P3_7_1.checked (bank 1 9) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_2100_439)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_1_9_2359_0 receipt_1_9_2359_1 receipt_1_9_2360_0 receipt_1_9_2360_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_2_9_2359_0 : fastPhase (bank 2 9).shape 179818 2359 10 1 0 7 0 = 124868418508611234465471870 :=
  phase_of_block (n := 440) (by decide +kernel)
    (CompactRank6970.from_blocks (f := fastLayer (bank 2 9).shape 179818 2359 10 1 0 7 0) (start := 0)
      [
      (128,65936520966250923607300611), (128,39684460283476939939836347),
      (128,17557655747052168537068104), (56,1689781511831202381266808)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel))

private theorem receipt_2_9_2359_1 : fastPhase (bank 2 9).shape 179818 2359 10 1 0 7 1 = 124245161166008219890152552 :=
  phase_of_block (n := 440) (by decide +kernel)
    (CompactRank6970.from_blocks (f := fastLayer (bank 2 9).shape 179818 2359 10 1 0 7 1) (start := 0)
      [
      (128,65716973382406922812256768), (128,39497756967435677622579186),
      (128,17400712323033475021462921), (56,1629718493132144433853677)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel))

private theorem receipt_2_9_2360_0 : fastPhase (bank 2 9).shape 179818 2360 10 1 0 7 0 = 124869368947775142788841843 :=
  phase_of_block (n := 440) (by decide +kernel)
    (CompactRank6970.from_blocks (f := fastLayer (bank 2 9).shape 179818 2360 10 1 0 7 0) (start := 0)
      [
      (128,65937090082934898153506880), (128,39684740231110518562562604),
      (128,17557750362758816234299128), (56,1689788270970909838473231)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel))

private theorem receipt_2_9_2360_1 : fastPhase (bank 2 9).shape 179818 2360 10 1 0 7 1 = 124246107911987614931667384 :=
  phase_of_block (n := 440) (by decide +kernel)
    (CompactRank6970.from_blocks (f := fastLayer (bank 2 9).shape 179818 2360 10 1 0 7 1) (start := 0)
      [
      (128,65717540920636085252339910), (128,39498035780858011964161386),
      (128,17400806184515804377096227), (56,1629725025977713338069861)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel))

theorem receipt_2_9 : Checked (bank 2 9) 10 0 7 := by
  refine checked_from_values (bank 2 9) 10 0 7
    (P3_7_1.checked (bank 2 9) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_2100_439)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_2_9_2359_0 receipt_2_9_2359_1 receipt_2_9_2360_0 receipt_2_9_2360_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_3_9_2359_0 : fastPhase (bank 3 9).shape 179818 2359 10 1 1 1 0 = 24341093532101439978941016 :=
  phase_of_block (n := 457) (by decide +kernel)
    (CompactRank6970.from_blocks (f := fastLayer (bank 3 9).shape 179818 2359 10 1 1 1 0) (start := 0)
      [
      (128,12532010027531974852577280), (128,7709428232332825285584896),
      (128,3597778473725725674391552), (73,501876798510914166387288)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel))

private theorem receipt_3_9_2359_1 : fastPhase (bank 3 9).shape 179818 2359 10 1 1 1 1 = 24223681863124717243261220 :=
  phase_of_block (n := 457) (by decide +kernel)
    (CompactRank6970.from_blocks (f := fastLayer (bank 3 9).shape 179818 2359 10 1 1 1 1) (start := 0)
      [
      (128,12492196209410559644794944), (128,7674765679009418031398976),
      (128,3568726755901711327952960), (73,487993218803028239114340)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel))

private theorem receipt_3_9_2360_0 : fastPhase (bank 3 9).shape 179818 2360 10 1 1 1 0 = 24341252479784454685899778 :=
  phase_of_block (n := 457) (by decide +kernel)
    (CompactRank6970.from_blocks (f := fastLayer (bank 3 9).shape 179818 2360 10 1 1 1 0) (start := 0)
      [
      (128,12532111900929779958838080), (128,7709472126429391146398528),
      (128,3597790812370381186134848), (73,501877640054902394528322)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel))

private theorem receipt_3_9_2360_1 : fastPhase (bank 3 9).shape 179818 2360 10 1 1 1 1 = 24223840095445456679672828 :=
  phase_of_block (n := 457) (by decide +kernel)
    (CompactRank6970.from_blocks (f := fastLayer (bank 3 9).shape 179818 2360 10 1 1 1 1) (start := 0)
      [
      (128,12492297713013484932987328), (128,7674809353761134848735680),
      (128,3568738989977324716063168), (73,487994038693512181886652)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel))

theorem receipt_3_9 : Checked (bank 3 9) 10 1 1 := by
  refine checked_from_values (bank 3 9) 10 1 1
    (P3_7_1.checked (bank 3 9) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_2091_456)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_3_9_2359_0 receipt_3_9_2359_1 receipt_3_9_2360_0 receipt_3_9_2360_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_0_10_2359_0 : fastPhase (bank 0 10).shape 179818 2359 20 1 0 1 0 = 4535339112348238262148534998 :=
  phase_of_block (n := 751) (by decide +kernel)
    (CompactRank6970.from_blocks (f := fastLayer (bank 0 10).shape 179818 2359 20 1 0 1 0) (start := 0)
      [
      (128,1515173245431121479961524288), (128,1175556049176800476343212096),
      (128,863663639942910089720723520), (128,578312722854639857040404738),
      (128,318325360448124137749080624), (111,84308094494642221333589732)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel))

private theorem receipt_0_10_2359_1 : fastPhase (bank 0 10).shape 179818 2359 20 1 0 1 1 = 4522223681780035675790297272 :=
  phase_of_block (n := 751) (by decide +kernel)
    (CompactRank6970.from_blocks (f := fastLayer (bank 0 10).shape 179818 2359 20 1 0 1 1) (start := 0)
      [
      (128,1512445528477536288465642880), (128,1173042161529669766375941504),
      (128,861354617199499189799740800), (128,576199637036888427129155354),
      (128,316399316040096845825844714), (111,82782421496345158193972020)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel))

private theorem receipt_0_10_2360_0 : fastPhase (bank 0 10).shape 179818 2360 20 1 0 1 0 = 4535373193524865425478033015 :=
  phase_of_block (n := 751) (by decide +kernel)
    (CompactRank6970.from_blocks (f := fastLayer (bank 0 10).shape 179818 2360 20 1 0 1 0) (start := 0)
      [
      (128,1515186660022553838289216896), (128,1175565378554412412867052928),
      (128,863669658425971262494811520), (128,578316163324497262446154395),
      (128,318326911641125217519850881), (111,84308421556305431860946395)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel))

private theorem receipt_0_10_2360_1 : fastPhase (bank 0 10).shape 179818 2360 20 1 0 1 1 = 4522257687725180157673050774 :=
  phase_of_block (n := 751) (by decide +kernel)
    (CompactRank6970.from_blocks (f := fastLayer (bank 0 10).shape 179818 2360 20 1 0 1 1) (start := 0)
      [
      (128,1512458923329108963923272320), (128,1173051474251614146195980928),
      (128,861360621918152042002768512), (128,576203066444004083094259123),
      (128,316400858708538300735290657), (111,82782743073762621721479234)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel))

theorem receipt_0_10 : Checked (bank 0 10) 20 0 1 := by
  refine checked_from_values (bank 0 10) 20 0 1
    (P3_7_1.checked (bank 0 10) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_3438_750)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_0_10_2359_0 receipt_0_10_2359_1 receipt_0_10_2360_0 receipt_0_10_2360_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_1_10_2359_0 : fastPhase (bank 1 10).shape 179818 2359 20 1 0 2 0 = 4038070190557592770966927082 :=
  phase_of_block (n := 751) (by decide +kernel)
    (CompactRank6970.from_blocks (f := fastLayer (bank 1 10).shape 179818 2359 20 1 0 2 0) (start := 0)
      [
      (128,1351281530868473181838317504), (128,1047151132107290405247285184),
      (128,768410646083053904353810368), (128,513920348163458358284942039),
      (128,282550237396785570406020423), (111,74756295938531350836551564)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel))

private theorem receipt_1_10_2359_1 : fastPhase (bank 1 10).shape 179818 2359 20 1 0 2 1 = 4026366526835941485530114599 :=
  phase_of_block (n := 751) (by decide +kernel)
    (CompactRank6970.from_blocks (f := fastLayer (bank 1 10).shape 179818 2359 20 1 0 2 1) (start := 0)
      [
      (128,1348836307544482124209161856), (128,1044902106159436310766077568),
      (128,766349159030718816952780416), (128,512037811803166264304809331),
      (128,280838130131726896226152686), (111,73403012166411073071132742)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel))

private theorem receipt_1_10_2360_0 : fastPhase (bank 1 10).shape 179818 2360 20 1 0 2 0 = 4038100543821211770198061276 :=
  phase_of_block (n := 751) (by decide +kernel)
    (CompactRank6970.from_blocks (f := fastLayer (bank 1 10).shape 179818 2360 20 1 0 2 0) (start := 0)
      [
      (128,1351293494564164768644482208), (128,1047159442543835610065245344),
      (128,768416000867083631527126176), (128,513923405607188167254735459),
      (128,282551614289118670026337155), (111,74756585949820922680134934)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel))

private theorem receipt_1_10_2360_1 : fastPhase (bank 1 10).shape 179818 2360 20 1 0 2 1 = 4026396812870283720025116615 :=
  phase_of_block (n := 751) (by decide +kernel)
    (CompactRank6970.from_blocks (f := fastLayer (bank 1 10).shape 179818 2360 20 1 0 2 1) (start := 0)
      [
      (128,1348848253524118292770966176), (128,1044910401682168930657278624),
      (128,766354501518542349757803168), (128,512040859387576244182267306),
      (128,280839499445040908277719138), (111,73403297312836994379082203)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel))

theorem receipt_1_10 : Checked (bank 1 10) 20 0 2 := by
  refine checked_from_values (bank 1 10) 20 0 2
    (P3_7_1.checked (bank 1 10) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_3438_750)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_1_10_2359_0 receipt_1_10_2359_1 receipt_1_10_2360_0 receipt_1_10_2360_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_2_10_2359_0 : fastPhase (bank 2 10).shape 179818 2359 20 1 0 7 0 = 1998422600822307330543028516 :=
  phase_of_block (n := 751) (by decide +kernel)
    (CompactRank6970.from_blocks (f := fastLayer (bank 2 10).shape 179818 2359 20 1 0 7 0) (start := 0)
      [
      (128,677075863410120128380076416), (128,520024129706878719768134016),
      (128,378191866741514882524840320), (128,250675391278133461917712355),
      (128,136597379413511140416765657), (111,35857970272148997535499752)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel))

private theorem receipt_2_10_2359_1 : fastPhase (bank 2 10).shape 179818 2359 20 1 0 7 1 = 1992532525671522094385640673 :=
  phase_of_block (n := 751) (by decide +kernel)
    (CompactRank6970.from_blocks (f := fastLayer (bank 2 10).shape 179818 2359 20 1 0 7 1) (start := 0)
      [
      (128,675803641804837860765717760), (128,518870958776741715810931968),
      (128,377150782116812169621853440), (128,249739628960433462543417407),
      (128,135760371723693934904932708), (111,35207142289002950738787390)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel))

private theorem receipt_2_10_2360_0 : fastPhase (bank 2 10).shape 179818 2360 20 1 0 7 0 = 1998437655415941745240702311 :=
  phase_of_block (n := 751) (by decide +kernel)
    (CompactRank6970.from_blocks (f := fastLayer (bank 2 10).shape 179818 2360 20 1 0 7 0) (start := 0)
      [
      (128,677081858413454352423067872), (128,520028257106974078343803104),
      (128,378194502510957733107908832), (128,250676882809493746076274660),
      (128,136598045178092876965897218), (111,35858109396968958323750625)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel))

private theorem receipt_2_10_2360_1 : fastPhase (bank 2 10).shape 179818 2360 20 1 0 7 1 = 1992547546073957086026456183 :=
  phase_of_block (n := 751) (by decide +kernel)
    (CompactRank6970.from_blocks (f := fastLayer (bank 2 10).shape 179818 2360 20 1 0 7 1) (start := 0)
      [
      (128,675809627514188234633268192), (128,518875078481686463139175392),
      (128,377153411649085348856228832), (128,249741115577726643924931941),
      (128,135761033778166560463763379), (111,35207279073103835009088447)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel))

theorem receipt_2_10 : Checked (bank 2 10) 20 0 7 := by
  refine checked_from_values (bank 2 10) 20 0 7
    (P3_7_1.checked (bank 2 10) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_3438_750)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_2_10_2359_0 receipt_2_10_2359_1 receipt_2_10_2360_0 receipt_2_10_2360_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_3_10_2359_0 : fastPhase (bank 3 10).shape 179818 2359 20 1 1 1 0 = 156684457788209028280440838 :=
  phase_of_block (n := 571) (by decide +kernel)
    (CompactRank6970.from_blocks (f := fastLayer (bank 3 10).shape 179818 2359 20 1 1 1 0) (start := 0)
      [
      (128,66874090523392123421200192), (128,46729833037835727145684800),
      (128,28726008568188300603592512), (128,12998174351443305936637760),
      (59,1356351307349571173325574)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel))

private theorem receipt_3_10_2359_1 : fastPhase (bank 3 10).shape 179818 2359 20 1 1 1 1 = 156083214378852850698725754 :=
  phase_of_block (n := 571) (by decide +kernel)
    (CompactRank6970.from_blocks (f := fastLayer (bank 3 10).shape 179818 2359 20 1 1 1 1) (start := 0)
      [
      (128,66710742945391105577685696), (128,46582054134760694122173120),
      (128,28594950726029621743522496), (128,12884972634871166048654016),
      (59,1310493937800263206690426)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel))

private theorem receipt_3_10_2360_0 : fastPhase (bank 3 10).shape 179818 2360 20 1 1 1 0 = 156685483463666023469058456 :=
  phase_of_block (n := 571) (by decide +kernel)
    (CompactRank6970.from_blocks (f := fastLayer (bank 3 10).shape 179818 2360 20 1 1 1 0) (start := 0)
      [
      (128,66874646312509603966419840), (128,46730132119632811894203264),
      (128,28726139973306965057979264), (128,12998211617623706423272320),
      (59,1356353440592936127183768)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel))

private theorem receipt_3_10_2360_1 : fastPhase (bank 3 10).shape 179818 2360 20 1 1 1 1 = 156084236377805537717073246 :=
  phase_of_block (n := 571) (by decide +kernel)
    (CompactRank6970.from_blocks (f := fastLayer (bank 3 10).shape 179818 2360 20 1 1 1 1) (start := 0)
      [
      (128,66711297179695962862004544), (128,46582352153930670814751040),
      (128,28595081474973087786379584), (128,12885009566842922310953280),
      (59,1310496002362893942984798)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel))

theorem receipt_3_10 : Checked (bank 3 10) 20 1 1 := by
  refine checked_from_values (bank 3 10) 20 1 1
    (P3_7_1.checked (bank 3 10) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_2726_570)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_3_10_2359_0 receipt_3_10_2359_1 receipt_3_10_2360_0 receipt_3_10_2360_1 (by decide +kernel) (by decide +kernel)

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

theorem group3_avoids {h : ℕ} {D : K1_14_1.PoleData h} (Crt : K1_14_1.CRTLift D)
    (word : K1.I → K1_14.L) (lo : 2359 ≤ h) (hi : h ≤ 33579) (rect : Fin 4)
    (i : Fin 3) {G : K1_14.Jet} (irr : Irreducible G) (seeded : K1_14_2.UsesSeed G)
    (slope : 1≤G.natDegree) (hs : seed rect≤K1_14_2_2_2_1.seedDegree G)
    (hj : G.natDegree+excess rect≤K1_14_2_2_2_1.jetDegree G) :
    ∃ Q ∈ K1_14_1.evaluated Crt word (bank rect (group3_stage i)).shape
      (cutoff h rect (group3_stage i)), ¬ G∣Q :=
  (group3_checked rect i).avoids Crt word lo hi irr seeded slope hs hj

end Lower6960.RescueSource
