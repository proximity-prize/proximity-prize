import ProximityPrize.SubmissionLower.Z6970CompactRankBlocks
import ProximityPrize.SubmissionLower.R6960RescueSourceReceipt1

set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 18000

namespace Lower6960.RescueSource
open P1_7 (Bank debit)
open P1_7_1_3 (blockEstimate block_append momentEstimate)
open HelperSource (WidthGuard)

theorem moment_3870_809 : momentEstimate 3870 809 = 5992280745484 :=
  CompactRank6970.from_blocks (f := P1_7_1_3.offsetEstimate 3870 809) (start := 809)
    [
      (128,1350454560), (128,9056935200), (128,23668288800), (128,44379208992), (128,70384389408),
      (128,100878523680), (128,134727508950), (128,167637366720), (128,197185337280),
      (128,223335921600), (128,246089119680), (128,265444931520), (128,281403357120),
      (128,293964396480), (128,303128049600), (128,308894316480), (128,311263197120),
      (128,310234691520), (128,305808799680), (128,297985521600), (128,286764857280),
      (128,272146806720), (128,254131369920), (128,232718829875), (128,208452439454),
      (128,183217087457), (128,157861267698), (128,132922472315), (128,108906379528),
      (128,86286851710), (128,65428117547), (128,46761079776), (128,30868837344), (128,18012681184),
      (128,8444269536), (128,2415260640), (71,121821510)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel)

theorem moment_4235_890 : momentEstimate 4235 890 = 8627387690344 :=
  CompactRank6970.from_blocks (f := P1_7_1_3.offsetEstimate 4235 890) (start := 890)
    [
      (128,1481036960), (128,9958958240), (128,26107212960), (128,49120494752), (128,78193497248),
      (128,112520914080), (128,151297321945), (128,192416653440), (128,230838968448),
      (128,265524158592), (128,296472223872), (128,323683164288), (128,347156979840),
      (128,366893670528), (128,382893236352), (128,395155677312), (128,403680993408),
      (128,408469184640), (128,409520251008), (128,406834192512), (128,400411009152),
      (128,390250700928), (128,376353267840), (128,358718709888), (128,337347027072),
      (128,312238219392), (128,283690141688), (128,253624141004), (128,223191153402),
      (128,192941946510), (128,163397461409), (128,135049716262), (128,108361807977),
      (128,83636873128), (128,61387552016), (128,42182088976), (128,26273545488), (128,13913579792),
      (128,5353850128), (128,846014736), (5,93131)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel)

theorem moment_4235_924 : momentEstimate 4235 924 = 8883701072242 :=
  CompactRank6970.from_blocks (f := P1_7_1_3.offsetEstimate 4235 924) (start := 924)
    [
      (128,1481036960), (128,9958958240), (128,26107212960), (128,49120494752), (128,78193497248),
      (128,112520914080), (128,151297438880), (128,193178402555), (128,233312350400),
      (128,269578744000), (128,301965406400), (128,330472337600), (128,355099537600),
      (128,375847006400), (128,392714744000), (128,405702750400), (128,414811025600),
      (128,420039569600), (128,421388382400), (128,418857464000), (128,412446814400),
      (128,402156433600), (128,387986321600), (128,369936478400), (128,348006904000),
      (128,322198666532), (128,293161594589), (128,262868460698), (128,232145769140),
      (128,201537973074), (128,171561665426), (128,142705580189), (128,115430591933),
      (128,90027048170), (128,67011238656), (128,46972332800), (128,30163499776), (128,16836397824),
      (128,7242685184), (128,1634020096), (39,23322080)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel)

theorem moment_4255_890 : momentEstimate 4255 890 = 8759063388784 :=
  CompactRank6970.from_blocks (f := P1_7_1_3.offsetEstimate 4255 890) (start := 890)
    [
      (128,1488192160), (128,10008384160), (128,26240852640), (128,49380291232), (128,78621393568),
      (128,113158853280), (128,152187246365), (128,193592488320), (128,232306766208),
      (128,267283919232), (128,298523947392), (128,326026850688), (128,349792629120),
      (128,369821282688), (128,386112811392), (128,398667215232), (128,407484494208),
      (128,412564648320), (128,413907677568), (128,411513581952), (128,405382361472),
      (128,395514016128), (128,381908545920), (128,364565950848), (128,343486230912),
      (128,318669386112), (128,290279870826), (128,260054586913), (128,229385819232),
      (128,198837794000), (128,168935971457), (128,140176889005), (128,113028162661),
      (128,87833864441), (128,65012280656), (128,45205207376), (128,28676703568), (128,15678427472),
      (128,6462037328), (128,1279191376), (25,6565356)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel)

theorem moment_4866_1061 : momentEstimate 4866 1061 = 15471861206598 :=
  CompactRank6970.from_blocks (f := P1_7_1_3.offsetEstimate 4866 1061) (start := 1061)
    [
      (128,1706783520), (128,11518346016), (128,30323544864), (128,57317073696), (128,91693626144),
      (128,132647895840), (128,179374576416), (128,231068361504), (128,286454620881),
      (128,340231189824), (128,389585745216), (128,434485949760), (128,474931803456),
      (128,510923306304), (128,542460458304), (128,569543259456), (128,592171709760),
      (128,610345809216), (128,624065557824), (128,633330955584), (128,638142002496),
      (128,638498698560), (128,634401043776), (128,625849038144), (128,612842681664),
      (128,595381974336), (128,573466916160), (128,547097507136), (128,516273747264),
      (128,481005997449), (128,442318295470), (128,402338149752), (128,361812541516),
      (128,321290189818), (128,281295549078), (128,242328807457), (128,204865888039),
      (128,169358449123), (128,136012354473), (128,105427402336), (128,78230822496),
      (128,54674308704), (128,35009519200), (128,19488112224), (128,8361746016), (128,1882078816),
      (39,26811510)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel)

private theorem receipt_0_11_2359_0 : fastPhase (bank 0 11).shape 179818 2359 32 1 0 1 0 = 33660689143245135698699460358 :=
  phase_of_block (n := 1062) (by decide +kernel)
    (CompactRank6970.from_blocks (f := fastLayer (bank 0 11).shape 179818 2359 32 1 0 1 0) (start := 0)
      [
      (128,8223917662167301636378211072), (128,6932281532071113723765535488),
      (128,5714799273932087588800443136), (128,4569266526745980816157127424),
      (128,3493485455570052288715567872), (128,2485265091603514067153637306),
      (128,1542422729904855029197305902), (128,662776108436828443392634598),
      (38,36474762813402105138997560)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel))

private theorem receipt_0_11_2359_1 : fastPhase (bank 0 11).shape 179818 2359 32 1 0 1 1 = 33591825055288519607034668076 :=
  phase_of_block (n := 1062) (by decide +kernel)
    (CompactRank6970.from_blocks (f := fastLayer (bank 0 11).shape 179818 2359 32 1 0 1 1) (start := 0)
      [
      (128,8213671477446542067420542784), (128,6922603675206956129450399552),
      (128,5705673053608926814857295680), (128,4560675301401983231175153472),
      (128,3485412633349040742995343168), (128,2477694129209102445978699852),
      (128,1535337122246621744246726996), (128,656159393426694410529876832),
      (38,34598269392652020380629740)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel))

private theorem receipt_0_11_2360_0 : fastPhase (bank 0 11).shape 179818 2360 32 1 0 1 0 = 33660941128604399982767708549 :=
  phase_of_block (n := 1062) (by decide +kernel)
    (CompactRank6970.from_blocks (f := fastLayer (bank 0 11).shape 179818 2360 32 1 0 1 0) (start := 0)
      [
      (128,8223991238768363826418525952), (128,6932339118049293691643152128),
      (128,5714842946989312146824619776), (128,4569298288574392816469083904),
      (128,3493507232079537546586236672), (128,2485278724776099012213327461),
      (128,1542429985002753694647724624), (128,662778710296731596642556488),
      (38,36474884067915651322481544)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel))

private theorem receipt_0_11_2360_1 : fastPhase (bank 0 11).shape 179818 2360 32 1 0 1 1 = 33592076647400794618432613622 :=
  phase_of_block (n := 1062) (by decide +kernel)
    (CompactRank6970.from_blocks (f := fastLayer (bank 0 11).shape 179818 2360 32 1 0 1 1) (start := 0)
      [
      (128,8213744979290624573149470976), (128,6922661194663907163704967424),
      (128,5705716668021472695813841152), (128,4560707012104312533278294272),
      (128,3485434365894329914585669888), (128,2477707725249803801566492668),
      (128,1535344346758345339724671915), (128,656161970880631364096838506),
      (38,34598384537367232512366821)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel))

theorem receipt_0_11 : Checked (bank 0 11) 32 0 1 := by
  refine checked_from_values (bank 0 11) 32 0 1
    (P3_7_1.checked (bank 0 11) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_4866_1061)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_0_11_2359_0 receipt_0_11_2359_1 receipt_0_11_2360_0 receipt_0_11_2360_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_1_11_2359_0 : fastPhase (bank 1 11).shape 179818 2359 32 1 0 2 0 = 29973256769847810071590924878 :=
  phase_of_block (n := 1062) (by decide +kernel)
    (CompactRank6970.from_blocks (f := fastLayer (bank 1 11).shape 179818 2359 32 1 0 2 0) (start := 0)
      [
      (128,7336862349088841112850262976), (128,6179126738870322052215720896),
      (128,5089450873008172622516300736), (128,4065700110812582031066500032),
      (128,3105752403194604422596357056), (128,2207498575089378896461548630),
      (128,1368843545125803449362102223), (128,587699365170910324986911035),
      (38,32322809487195159535221294)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel))

private theorem receipt_1_11_2359_1 : fastPhase (bank 1 11).shape 179818 2359 32 1 0 2 1 = 29911793300376349122971019273 :=
  phase_of_block (n := 1062) (by decide +kernel)
    (CompactRank6970.from_blocks (f := fastLayer (bank 1 11).shape 179818 2359 32 1 0 2 1) (start := 0)
      [
      (128,7327671183634436137027609344), (128,6170458053787639724055536384),
      (128,5081288467913159482086695680), (128,4058027881383460230554198784),
      (128,3098554340979411561713345280), (128,2200758766336642942447635653),
      (128,1362546161439698824078625103), (128,581828667685449917769567826),
      (38,30659777216450303237805219)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel))

private theorem receipt_1_11_2360_0 : fastPhase (bank 1 11).shape 179818 2360 32 1 0 2 0 = 29973481219127074316210382978 :=
  phase_of_block (n := 1062) (by decide +kernel)
    (CompactRank6970.from_blocks (f := fastLayer (bank 1 11).shape 179818 2360 32 1 0 2 0) (start := 0)
      [
      (128,7336927989843568286166143616), (128,6179178068739203108077408896),
      (128,5089489767344268115684315776), (128,4065728372466471251548639872),
      (128,3105771762951573209083990656), (128,2207510684670524234119284342),
      (128,1368849983838420569919425238), (128,587701672333717660771771788),
      (38,32322916939327880839402794)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel))

private theorem receipt_1_11_2360_1 : fastPhase (bank 1 11).shape 179818 2360 32 1 0 2 1 = 29912017398147719606032082589 :=
  phase_of_block (n := 1062) (by decide +kernel)
    (CompactRank6970.from_blocks (f := fastLayer (bank 1 11).shape 179818 2360 32 1 0 2 1) (start := 0)
      [
      (128,7327736757246395903937140736), (128,6170509324010818136812050432),
      (128,5081327309755200452671297536), (128,4058056097351924991348135936),
      (128,3098573661518961256254068736), (128,2200770842853180907388874126),
      (128,1362552572964697617051251442), (128,581830953192756092875717680),
      (38,30659879253784247693545965)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel))

theorem receipt_1_11 : Checked (bank 1 11) 32 0 2 := by
  refine checked_from_values (bank 1 11) 32 0 2
    (P3_7_1.checked (bank 1 11) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_4866_1061)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_1_11_2359_0 receipt_1_11_2359_1 receipt_1_11_2360_0 receipt_1_11_2360_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_2_11_2359_0 : fastPhase (bank 2 11).shape 179818 2359 32 1 0 7 0 = 14849183624768987533235392190 :=
  phase_of_block (n := 1062) (by decide +kernel)
    (CompactRank6970.from_blocks (f := fastLayer (bank 2 11).shape 179818 2359 32 1 0 7 0) (start := 0)
      [
      (128,3686444713139156897548297728), (128,3084455990531416323198019072),
      (128,2523852479522594582306121216), (128,2002895391531102981431551488),
      (128,1519882054311926139025057280), (128,1073145753237820217052697138),
      (128,661056020162432528139441978), (128,282014975969196893168830530),
      (38,15436246363340971365375760)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel))

private theorem receipt_2_11_2359_1 : fastPhase (bank 2 11).shape 179818 2359 32 1 0 7 1 = 14818198759828604233033488672 :=
  phase_of_block (n := 1062) (by decide +kernel)
    (CompactRank6970.from_blocks (f := fastLayer (bank 2 11).shape 179818 2359 32 1 0 7 1) (start := 0)
      [
      (128,3681638502969206592263207744), (128,3079970775450547911996152640),
      (128,2519674910748352679995865920), (128,1999012397005828308946639680),
      (128,1516280836345118507155995456), (128,1069813785666951338372087600),
      (128,657981041551720538832994528), (128,279184989608706089815245288),
      (38,14641520482172265655299816)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel))

private theorem receipt_2_11_2360_0 : fastPhase (bank 2 11).shape 179818 2360 32 1 0 7 0 = 14849295073656338181377607277 :=
  phase_of_block (n := 1062) (by decide +kernel)
    (CompactRank6970.from_blocks (f := fastLayer (bank 2 11).shape 179818 2360 32 1 0 7 0) (start := 0)
      [
      (128,3686477695940188192045755648), (128,3084481614141493739193076992),
      (128,2523871768118595913292426496), (128,2002909314916779304139083008),
      (128,1519891529139073887413464320), (128,1073151640609191486773859165),
      (128,661059129905102497339905288), (128,282016083206727813704181560),
      (38,15436297679185347475854800)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel))

private theorem receipt_2_11_2360_1 : fastPhase (bank 2 11).shape 179818 2360 32 1 0 7 1 = 14818310029569716465714973050 :=
  phase_of_block (n := 1062) (by decide +kernel)
    (CompactRank6970.from_blocks (f := fastLayer (bank 2 11).shape 179818 2360 32 1 0 7 1) (start := 0)
      [
      (128,3681671450349599040800527616), (128,3079996367972477486052242688),
      (128,2519694172318651746267649280), (128,1999026297164975302299170048),
      (128,1516290291488346026782954752), (128,1069819656658460756344694420),
      (128,657984138004316341769784691), (128,279186086402567226711072010),
      (38,14641569210322538686877545)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel))

theorem receipt_2_11 : Checked (bank 2 11) 32 0 7 := by
  refine checked_from_values (bank 2 11) 32 0 7
    (P3_7_1.checked (bank 2 11) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_4866_1061)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_2_11_2359_0 receipt_2_11_2359_1 receipt_2_11_2360_0 receipt_2_11_2360_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_3_11_2359_0 : fastPhase (bank 3 11).shape 179818 2359 32 1 1 1 0 = 1242835493235765842258685801 :=
  phase_of_block (n := 810) (by decide +kernel)
    (CompactRank6970.from_blocks (f := fastLayer (bank 3 11).shape 179818 2359 32 1 1 1 0) (start := 0)
      [
      (128,391365608946557058575785248), (128,309518662692320100481191200),
      (128,233455084584970005594127648), (128,163442140247102735226842400),
      (128,99744143792435902157430048), (128,42622467280157414154767648),
      (42,2687385692222626068541609)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel))

private theorem receipt_3_11_2359_1 : fastPhase (bank 3 11).shape 179818 2359 32 1 1 1 1 = 1239471713883594216371155029 :=
  phase_of_block (n := 810) (by decide +kernel)
    (CompactRank6970.from_blocks (f := fastLayer (bank 3 11).shape 179818 2359 32 1 1 1 1) (start := 0)
      [
      (128,390712621740650783517993632), (128,308908013482996718285642400),
      (128,232889040468343350163425952), (128,162922944029370109298227872),
      (128,99274014066658142501481120), (128,42203598503038956774103712),
      (42,2561481592536155830280341)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel))

private theorem receipt_3_11_2360_0 : fastPhase (bank 3 11).shape 179818 2360 32 1 1 1 0 = 1242843594654362360920877844 :=
  phase_of_block (n := 810) (by decide +kernel)
    (CompactRank6970.from_blocks (f := fastLayer (bank 3 11).shape 179818 2360 32 1 1 1 0) (start := 0)
      [
      (128,391368952570786218831926592), (128,309520883991675493791094080),
      (128,233456449974934589801977152), (128,163442885546509226433172800),
      (128,99744474512063975437653312), (128,42622558910451294975481152),
      (42,2687389147941561649572756)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel))

private theorem receipt_3_11_2360_1 : fastPhase (bank 3 11).shape 179818 2360 32 1 1 1 1 = 1239479794830088271991583044 :=
  phase_of_block (n := 810) (by decide +kernel)
    (CompactRank6970.from_blocks (f := fastLayer (bank 3 11).shape 179818 2360 32 1 1 1 1) (start := 0)
      [
      (128,390715958945341813195349952), (128,308910229800011316852465600),
      (128,232890402144062822652583872), (128,162923686715277188124614592),
      (128,99274343107928553183453120), (128,42203689226253374352695232),
      (42,2561484891213203630420676)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel))

theorem receipt_3_11 : Checked (bank 3 11) 32 1 1 := by
  refine checked_from_values (bank 3 11) 32 1 1
    (P3_7_1.checked (bank 3 11) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_3870_809)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_3_11_2359_0 receipt_3_11_2359_1 receipt_3_11_2360_0 receipt_3_11_2360_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_0_12_2359_0 : fastPhase (bank 0 12).shape 179818 2359 31 1 0 1 0 = 18327076493355066686497722098 :=
  phase_of_block (n := 891) (by decide +kernel)
    (CompactRank6970.from_blocks (f := fastLayer (bank 0 12).shape 179818 2359 31 1 0 1 0) (start := 0)
      [
      (128,5238026383535905637951615591), (128,4260963754497660576817200014),
      (128,3348355294707772099558881242), (128,2497995112038295845878073355),
      (128,1707683778691791497274232590), (128,975228415734354362510410619),
      (123,298823754149286666507308687)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel))

private theorem receipt_0_12_2359_1 : fastPhase (bank 0 12).shape 179818 2359 31 1 0 1 1 = 18282563063587017403936991164 :=
  phase_of_block (n := 891) (by decide +kernel)
    (CompactRank6970.from_blocks (f := fastLayer (bank 0 12).shape 179818 2359 31 1 0 1 1) (start := 0)
      [
      (128,5230238641527756557211197671), (128,4253670862945832398742975457),
      (128,3341540589014195479468697015), (128,2491641977404755783391043624),
      (128,1701775650174768583590157018), (128,969748778193986902319317809),
      (123,293946564325721699213602570)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel))

private theorem receipt_0_12_2360_0 : fastPhase (bank 0 12).shape 179818 2360 31 1 0 1 0 = 18327214102873882765583798724 :=
  phase_of_block (n := 891) (by decide +kernel)
    (CompactRank6970.from_blocks (f := fastLayer (bank 0 12).shape 179818 2360 31 1 0 1 0) (start := 0)
      [
      (128,5238072967468954182509421930), (128,4260998414332550676093255249),
      (128,3348379878009440074717584588), (128,2498011390680185019765721605),
      (128,1707693443395740310380838014), (128,975233074464085002510767849),
      (123,298824934522927499606209489)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel))

private theorem receipt_0_12_2360_1 : fastPhase (bank 0 12).shape 179818 2360 31 1 0 1 1 = 18282700415733949553918024625 :=
  phase_of_block (n := 891) (by decide +kernel)
    (CompactRank6970.from_blocks (f := fastLayer (bank 0 12).shape 179818 2360 31 1 0 1 1) (start := 0)
      [
      (128,5230285168539515388866116246), (128,4253705473165379904432298385),
      (128,3341565129638853643830047315), (128,2491658219934538054696811854),
      (128,1701785284957156943351190655), (128,969753412821141685694905548),
      (123,293947726677363933046654622)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel))

theorem receipt_0_12 : Checked (bank 0 12) 31 0 1 := by
  refine checked_from_values (bank 0 12) 31 0 1
    (P3_7_1.checked (bank 0 12) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_4255_890)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_0_12_2359_0 receipt_0_12_2359_1 receipt_0_12_2360_0 receipt_0_12_2360_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_1_12_2359_0 : fastPhase (bank 1 12).shape 179818 2359 31 1 0 2 0 = 16494037572303343786654768185 :=
  phase_of_block (n := 891) (by decide +kernel)
    (CompactRank6970.from_blocks (f := fastLayer (bank 1 12).shape 179818 2359 31 1 0 2 0) (start := 0)
      [
      (128,4721214711749797971412941417), (128,3837238032519095572824061607),
      (128,3012778529881408927325394126), (128,2245702986642540076728367063),
      (128,1533890777339338846605345192), (128,875233924931317054148399109),
      (123,267978609239845337610259671)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel))

private theorem receipt_1_12_2359_1 : fastPhase (bank 1 12).shape 179818 2359 31 1 0 2 1 = 16453898761115778681793170603 :=
  phase_of_block (n := 891) (by decide +kernel)
    (CompactRank6970.from_blocks (f := fastLayer (bank 1 12).shape 179818 2359 31 1 0 2 1) (start := 0)
      [
      (128,4714163541870090969739135953), (128,3830644515231329739299029703),
      (128,3006626511937896598756465357), (128,2239976411234220892678574826),
      (128,1528573683996401914124528967), (128,870310449327819078213574307),
      (123,263603647518019488981861490)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel))

private theorem receipt_1_12_2360_0 : fastPhase (bank 1 12).shape 179818 2360 31 1 0 2 0 = 16494161448857557939694459632 :=
  phase_of_block (n := 891) (by decide +kernel)
    (CompactRank6970.from_blocks (f := fastLayer (bank 1 12).shape 179818 2360 31 1 0 2 0) (start := 0)
      [
      (128,4721256699714712325018626677), (128,3837269245869121997209793668),
      (128,3012800649586828204436661696), (128,2245717621313332283198217507),
      (128,1533899458551823420153594356), (128,875238106037078085888248274),
      (123,267979667784661623789317454)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel))

private theorem receipt_1_12_2360_1 : fastPhase (bank 1 12).shape 179818 2360 31 1 0 2 1 = 16454022405316240686251072274 :=
  phase_of_block (n := 891) (by decide +kernel)
    (CompactRank6970.from_blocks (f := fastLayer (bank 1 12).shape 179818 2360 31 1 0 2 1) (start := 0)
      [
      (128,4714205478246567936112077108), (128,3830675683689207993461288892),
      (128,3006648593094092085667388361), (128,2239991013341422872458401083),
      (128,1528582338274160067719393385), (128,870314608774822583068702209),
      (123,263604689895967147763821236)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel))

theorem receipt_1_12 : Checked (bank 1 12) 31 0 2 := by
  refine checked_from_values (bank 1 12) 31 0 2
    (P3_7_1.checked (bank 1 12) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_4255_890)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_1_12_2359_0 receipt_1_12_2359_1 receipt_1_12_2360_0 receipt_1_12_2360_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_2_12_2359_0 : fastPhase (bank 2 12).shape 179818 2359 31 1 0 7 0 = 8872564966353450360433379584 :=
  phase_of_block (n := 891) (by decide +kernel)
    (CompactRank6970.from_blocks (f := fastLayer (bank 2 12).shape 179818 2359 31 1 0 7 0) (start := 0)
      [
      (128,2566992499620178669054878720), (128,2073546078246927338452755456),
      (128,1617988106630817799293363200), (128,1198574232054546006739035136),
      (128,813596852881844152128392670), (128,461385362515284347962322600),
      (123,140481834403852046802631802)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel))

private theorem receipt_2_12_2359_1 : fastPhase (bank 2 12).shape 179818 2359 31 1 0 7 1 = 8850673339054901114152263434 :=
  phase_of_block (n := 891) (by decide +kernel)
    (CompactRank6970.from_blocks (f := fastLayer (bank 2 12).shape 179818 2359 31 1 0 7 1) (start := 0)
      [
      (128,2563035313650856272056001600), (128,2069883095187150343101482048),
      (128,1614605942433324583051879488), (128,1195459784008118760546026560),
      (128,810737297166769717995400894), (128,458768148146444522978578284),
      (123,138183758462236914422894560)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel))

private theorem receipt_2_12_2360_0 : fastPhase (bank 2 12).shape 179818 2360 31 1 0 7 0 = 8872631279443071375999866499 :=
  phase_of_block (n := 891) (by decide +kernel)
    (CompactRank6970.from_blocks (f := fastLayer (bank 2 12).shape 179818 2360 31 1 0 7 0) (start := 0)
      [
      (128,2567015115387745966475753760), (128,2073562815861958262891120928),
      (128,1617999919365788282293082400), (128,1198582017866633492346317088),
      (128,813601454766387399286946013), (128,461387566828041676083382895),
      (123,140482389366516296623263415)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel))

private theorem receipt_2_12_2360_1 : fastPhase (bank 2 12).shape 179818 2360 31 1 0 7 1 = 8850739525008277395433061120 :=
  phase_of_block (n := 891) (by decide +kernel)
    (CompactRank6970.from_blocks (f := fastLayer (bank 2 12).shape 179818 2360 31 1 0 7 1) (start := 0)
      [
      (128,2563057900542065993023093920), (128,2069899807921376586133449888),
      (128,1614617734010016933075442848), (128,1195467552118338394457246880),
      (128,810741884549995307230466169), (128,458770340936310021290175873),
      (123,138184304930174160223185542)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel))

theorem receipt_2_12 : Checked (bank 2 12) 31 0 7 := by
  refine checked_from_values (bank 2 12) 31 0 7
    (P3_7_1.checked (bank 2 12) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_4235_890)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_2_12_2359_0 receipt_2_12_2359_1 receipt_2_12_2360_0 receipt_2_12_2360_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_3_12_2359_0 : fastPhase (bank 3 12).shape 179818 2359 31 1 1 1 0 = 1684334238450222833949307755 :=
  phase_of_block (n := 925) (by decide +kernel)
    (CompactRank6970.from_blocks (f := fastLayer (bank 3 12).shape 179818 2359 31 1 1 1 0) (start := 0)
      [
      (128,473279862205441242332640608), (128,385970195806973950209779040),
      (128,304251393533293143783576928), (128,228350435242021809516889440),
      (128,158491559809689204918220128), (128,94896274586079502066656608),
      (128,37783364848580431136806240), (29,1311152418143549984738763)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel))

private theorem receipt_3_12_2359_1 : fastPhase (bank 3 12).shape 179818 2359 31 1 1 1 1 = 1680315587253232572086908695 :=
  phase_of_block (n := 925) (by decide +kernel)
    (CompactRank6970.from_blocks (f := fastLayer (bank 3 12).shape 179818 2359 31 1 1 1 1) (start := 0)
      [
      (128,472585650103495907215375712), (128,385317023863689726742269280),
      (128,303641193409546074773888352), (128,227785116029364054285790560),
      (128,157973008107129104497884512), (128,94426354576861644399365472),
      (128,37363918376965716273651040), (29,1223322786180343898683767)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel))

private theorem receipt_3_12_2360_0 : fastPhase (bank 3 12).shape 179818 2360 31 1 1 1 0 = 1684345096457878381577422155 :=
  phase_of_block (n := 925) (by decide +kernel)
    (CompactRank6970.from_blocks (f := fastLayer (bank 3 12).shape 179818 2360 31 1 1 1 0) (start := 0)
      [
      (128,473283939176506932391880928), (128,385973040122052486453876960),
      (128,304253266456325477996038368), (128,228351571004530989948123360),
      (128,158492165881218661435009248), (128,94896531943751721999407328),
      (128,37783428245776025824577760), (29,1311153627716085528508203)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel))

private theorem receipt_3_12_2360_1 : fastPhase (bank 3 12).shape 179818 2360 31 1 1 1 1 = 1680326421126712082405821755 :=
  phase_of_block (n := 925) (by decide +kernel)
    (CompactRank6970.from_blocks (f := fastLayer (bank 3 12).shape 179818 2360 31 1 1 1 1) (start := 0)
      [
      (128,472589720165856551825091168), (128,385319862674103390458387040),
      (128,303643062082337839901870688), (128,227786248648083053247232608),
      (128,157973611994981169982892640), (128,94426610566262350216714848),
      (128,37363981078213808898722400), (29,1223323916873917874910363)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel))

theorem receipt_3_12 : Checked (bank 3 12) 31 1 1 := by
  refine checked_from_values (bank 3 12) 31 1 1
    (P3_7_1.checked (bank 3 12) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_4235_924)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_3_12_2359_0 receipt_3_12_2359_1 receipt_3_12_2360_0 receipt_3_12_2360_1 (by decide +kernel) (by decide +kernel)

def group4_stage (i : Fin 2) : Fin 17 :=
  ⟨11+i.val, by have := i.isLt; omega⟩

theorem group4_checked (rect : Fin 4) (i : Fin 2) :
    Checked (bank rect (group4_stage i)) (reserve (group4_stage i))
      (excess rect) (seed rect) := by
  fin_cases i
  · fin_cases rect
    · exact receipt_0_11
    · exact receipt_1_11
    · exact receipt_2_11
    · exact receipt_3_11
  · fin_cases rect
    · exact receipt_0_12
    · exact receipt_1_12
    · exact receipt_2_12
    · exact receipt_3_12

theorem group4_avoids {h : ℕ} {D : K1_14_1.PoleData h} (Crt : K1_14_1.CRTLift D)
    (word : K1.I → K1_14.L) (lo : 2359 ≤ h) (hi : h ≤ 33579) (rect : Fin 4)
    (i : Fin 2) {G : K1_14.Jet} (irr : Irreducible G) (seeded : K1_14_2.UsesSeed G)
    (slope : 1≤G.natDegree) (hs : seed rect≤K1_14_2_2_2_1.seedDegree G)
    (hj : G.natDegree+excess rect≤K1_14_2_2_2_1.jetDegree G) :
    ∃ Q ∈ K1_14_1.evaluated Crt word (bank rect (group4_stage i)).shape
      (cutoff h rect (group4_stage i)), ¬ G∣Q :=
  (group4_checked rect i).avoids Crt word lo hi irr seeded slope hs hj

end Lower6960.RescueSource
