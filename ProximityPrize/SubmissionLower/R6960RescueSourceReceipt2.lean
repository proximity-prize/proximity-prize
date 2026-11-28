import ProximityPrize.SubmissionLower.Z6970CompactRankBlocks
import ProximityPrize.SubmissionLower.R6960RescueSourceReceipt1

set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 18000

namespace Lower6960.RescueSource
open P1_7 (Bank debit)
open P1_7_1_3 (blockEstimate block_append momentEstimate)
open HelperSource (WidthGuard)

theorem moment_1696_356 : momentEstimate 1696 356 = 222371564601 :=
  CompactRank6970.from_blocks (f := P1_7_1_3.offsetEstimate 1696 356) (start := 356)
    [
      (128,572684320), (128,3684337696), (128,9136834131), (128,15370032384), (128,20341757184),
      (128,23816115456), (128,25793107200), (128,26272732416), (128,25254991104), (128,22739883264),
      (128,18755777396), (128,13945647249), (128,9230875643), (128,5110148823), (128,2022537952),
      (128,324080352), (4,22031)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel)

theorem moment_1696_370 : momentEstimate 1696 370 = 229159736517 :=
  CompactRank6970.from_blocks (f := P1_7_1_3.offsetEstimate 1696 370) (start := 370)
    [
      (128,572684320), (128,3684337696), (128,9141056804), (128,15557757376), (128,20767001024),
      (128,24420157888), (128,26517227968), (128,27058211264), (128,26043107776), (128,23471917504),
      (128,19393615038), (128,14532053576), (128,9746328986), (128,5521630460), (128,2297261808),
      (128,434348784), (18,1038245)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel)

theorem moment_1809_380 : momentEstimate 1809 380 = 287901786632 :=
  CompactRank6970.from_blocks (f := P1_7_1_3.offsetEstimate 1809 380) (start := 380)
    [
      (128,613111200), (128,3963594144), (128,9896705511), (128,17097207360), (128,23183453760),
      (128,27671670336), (128,30561857088), (128,31854014016), (128,31548141120), (128,29644238400),
      (128,26142305856), (128,21163152440), (128,15641164329), (128,10359919872), (128,5784462598),
      (128,2356385168), (128,419948944), (13,454490)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel)

theorem moment_1809_395 : momentEstimate 1809 395 = 296724029248 :=
  CompactRank6970.from_blocks (f := P1_7_1_3.offsetEstimate 1809 395) (start := 395)
    [
      (128,613111200), (128,3963594144), (128,9896719776), (128,17253050925), (128,23627260800),
      (128,28340839296), (128,31393473408), (128,32785163136), (128,32515908480), (128,30585709440),
      (128,26994566016), (128,21919153025), (128,16340444489), (128,10971561561), (128,6272279892),
      (128,2685846592), (128,561511488), (28,3835580)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel)

theorem moment_1817_380 : momentEstimate 1817 380 = 292013331876 :=
  CompactRank6970.from_blocks (f := P1_7_1_3.offsetEstimate 1817 380) (start := 380)
    [
      (128,615973280), (128,3983364512), (128,9950161303), (128,17198059584), (128,23334244416),
      (128,27872399424), (128,30812524608), (128,32154619968), (128,31898685504), (128,30044721216),
      (128,26592727104), (128,21638440059), (128,16076646528), (128,10730530099), (128,6072063646),
      (128,2541701328), (128,494759120), (21,1710177)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel)

theorem moment_2285_480 : momentEstimate 2285 480 = 732176567216 :=
  CompactRank6970.from_blocks (f := P1_7_1_3.offsetEstimate 2285 480) (start := 480)
    [
      (128,783404960), (128,5139931040), (128,13077344160), (128,23780618088), (128,35332736192),
      (128,45144212672), (128,52938228928), (128,58714784960), (128,62473880768), (128,64215516352),
      (128,63939691712), (128,61646406848), (128,57335661760), (128,51007456448), (128,42848244955),
      (128,34024165326), (128,25358865055), (128,17353338622), (128,10420160528), (128,5035269136),
      (128,1515991056), (77,90657650)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel)

theorem moment_2285_498 : momentEstimate 2285 498 = 753510622290 :=
  CompactRank6970.from_blocks (f := P1_7_1_3.offsetEstimate 2285 498) (start := 498)
    [
      (128,783404960), (128,5139931040), (128,13077344160), (128,23789529417), (128,35672256512),
      (128,45924478976), (128,54083743744), (128,60150050816), (128,64123400192), (128,66003791872),
      (128,65791225856), (128,63485702144), (128,59087220736), (128,52595798457), (128,44296056302),
      (128,35392420168), (128,26610909096), (128,18448620482), (128,11312632000), (128,5685571776),
      (128,1888735424), (95,167798160)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel)

private theorem receipt_0_5_2359_0 : fastPhase (bank 0 5).shape 179818 2359 5 1 0 1 0 = 52209815748559027184910222 :=
  phase_of_block (n := 357) (by decide +kernel)
    (CompactRank6970.from_blocks (f := fastLayer (bank 0 5).shape 179818 2359 5 1 0 1 0) (start := 0)
      [
      (128,32090974217140337048559616), (128,16444188410928575317060663),
      (101,3674653120490114819289943)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel))

private theorem receipt_0_5_2359_1 : fastPhase (bank 0 5).shape 179818 2359 5 1 0 1 1 = 51893771075761025830532589 :=
  phase_of_block (n := 357) (by decide +kernel)
    (CompactRank6970.from_blocks (f := fastLayer (bank 0 5).shape 179818 2359 5 1 0 1 1) (start := 0)
      [
      (128,31959412462546846365865344), (128,16333510924268776573255875),
      (101,3600847688945402891411370)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel))

private theorem receipt_0_5_2360_0 : fastPhase (bank 0 5).shape 179818 2360 5 1 0 1 0 = 52210213658627101234930350 :=
  phase_of_block (n := 357) (by decide +kernel)
    (CompactRank6970.from_blocks (f := fastLayer (bank 0 5).shape 179818 2360 5 1 0 1 0) (start := 0)
      [
      (128,32091246487400997903568960), (128,16444296591815446334974448),
      (101,3674670579410656996386942)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel))

private theorem receipt_0_5_2360_1 : fastPhase (bank 0 5).shape 179818 2360 5 1 0 1 1 = 51894167118197107402644213 :=
  phase_of_block (n := 357) (by decide +kernel)
    (CompactRank6970.from_blocks (f := fastLayer (bank 0 5).shape 179818 2360 5 1 0 1 1) (start := 0)
      [
      (128,31959683807434762056946880), (128,16333618475413542895298770),
      (101,3600864835348802450398563)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel))

theorem receipt_0_5 : Checked (bank 0 5) 5 0 1 := by
  refine checked_from_values (bank 0 5) 5 0 1
    (P3_7_1.checked (bank 0 5) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1696_356)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_0_5_2359_0 receipt_0_5_2359_1 receipt_0_5_2360_0 receipt_0_5_2360_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_1_5_2359_0 : fastPhase (bank 1 5).shape 179818 2359 5 1 0 2 0 = 46902468021115317962559336 :=
  phase_of_block (n := 357) (by decide +kernel)
    (CompactRank6970.from_blocks (f := fastLayer (bank 1 5).shape 179818 2359 5 1 0 2 0) (start := 0)
      [
      (128,28861436947913444218583488), (128,14751765671627144305622983),
      (101,3289265401574729438352865)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel))

private theorem receipt_1_5_2359_1 : fastPhase (bank 1 5).shape 179818 2359 5 1 0 2 1 = 46617888469656701498472741 :=
  phase_of_block (n := 357) (by decide +kernel)
    (CompactRank6970.from_blocks (f := fastLayer (bank 1 5).shape 179818 2359 5 1 0 2 1) (start := 0)
      [
      (128,28742538543763505459069184), (128,14652194130046026255274881),
      (101,3223155795847169784128676)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel))

private theorem receipt_1_5_2360_0 : fastPhase (bank 1 5).shape 179818 2360 5 1 0 2 0 = 46902825584266991849725077 :=
  phase_of_block (n := 357) (by decide +kernel)
    (CompactRank6970.from_blocks (f := fastLayer (bank 1 5).shape 179818 2360 5 1 0 2 0) (start := 0)
      [
      (128,28861681829159471843282944), (128,14751862724961680602094954),
      (101,3289281030145839404347179)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel))

private theorem receipt_1_5_2360_1 : fastPhase (bank 1 5).shape 179818 2360 5 1 0 2 1 = 46618244348789406443472624 :=
  phase_of_block (n := 357) (by decide +kernel)
    (CompactRank6970.from_blocks (f := fastLayer (bank 1 5).shape 179818 2360 5 1 0 2 1) (start := 0)
      [
      (128,28742782587822503531127680), (128,14652290616529863122750911),
      (101,3223171144437039789594033)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel))

theorem receipt_1_5 : Checked (bank 1 5) 5 0 2 := by
  refine checked_from_values (bank 1 5) 5 0 2
    (P3_7_1.checked (bank 1 5) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1696_356)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_1_5_2359_0 receipt_1_5_2359_1 receipt_1_5_2360_0 receipt_1_5_2360_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_2_5_2359_0 : fastPhase (bank 2 5).shape 179818 2359 5 1 0 7 0 = 24782189218028098801387691 :=
  phase_of_block (n := 357) (by decide +kernel)
    (CompactRank6970.from_blocks (f := fastLayer (bank 2 5).shape 179818 2359 5 1 0 7 0) (start := 0)
      [
      (128,15374571540781802447333568), (128,7714755793333521272996496),
      (101,1692861883912775081057627)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel))

private theorem receipt_2_5_2359_1 : fastPhase (bank 2 5).shape 179818 2359 5 1 0 7 1 = 24629281253259065553261147 :=
  phase_of_block (n := 357) (by decide +kernel)
    (CompactRank6970.from_blocks (f := fastLayer (bank 2 5).shape 179818 2359 5 1 0 7 1) (start := 0)
      [
      (128,15309016971635925313804672), (128,7661595948710983655366890),
      (101,1658668332912156584089585)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel))

private theorem receipt_2_5_2360_0 : fastPhase (bank 2 5).shape 179818 2360 5 1 0 7 0 = 24782378537300313380025718 :=
  phase_of_block (n := 357) (by decide +kernel)
    (CompactRank6970.from_blocks (f := fastLayer (bank 2 5).shape 179818 2360 5 1 0 7 0) (start := 0)
      [
      (128,15374702033669311636576800), (128,7714806573645479281186607),
      (101,1692869929985522462262311)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel))

private theorem receipt_2_5_2360_1 : fastPhase (bank 2 5).shape 179818 2360 5 1 0 7 1 = 24629469658775263458482610 :=
  phase_of_block (n := 357) (by decide +kernel)
    (CompactRank6970.from_blocks (f := fastLayer (bank 2 5).shape 179818 2360 5 1 0 7 1) (start := 0)
      [
      (128,15309146999550437747179680), (128,7661646425245799792641497),
      (101,1658676233979025918661433)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel))

theorem receipt_2_5 : Checked (bank 2 5) 5 0 7 := by
  refine checked_from_values (bank 2 5) 5 0 7
    (P3_7_1.checked (bank 2 5) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1696_356)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_2_5_2359_0 receipt_2_5_2359_1 receipt_2_5_2360_0 receipt_2_5_2360_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_3_5_2359_0 : fastPhase (bank 3 5).shape 179818 2359 5 1 1 1 0 = 6235887735099074744019349 :=
  phase_of_block (n := 371) (by decide +kernel)
    (CompactRank6970.from_blocks (f := fastLayer (bank 3 5).shape 179818 2359 5 1 1 1 0) (start := 0)
      [
      (128,3772041337147178468052448), (128,1960040005477657700589024),
      (115,503806392474238575377877)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel))

private theorem receipt_3_5_2359_1 : fastPhase (bank 3 5).shape 179818 2359 5 1 1 1 1 = 6198842374770738444931137 :=
  phase_of_block (n := 371) (by decide +kernel)
    (CompactRank6970.from_blocks (f := fastLayer (bank 3 5).shape 179818 2359 5 1 1 1 1) (start := 0)
      [
      (128,3756785034142476698368800), (128,1947311365606146921638688),
      (115,494745975022114824923649)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel))

private theorem receipt_3_5_2360_0 : fastPhase (bank 3 5).shape 179818 2360 5 1 1 1 0 = 6235928883803974331340693 :=
  phase_of_block (n := 371) (by decide +kernel)
    (CompactRank6970.from_blocks (f := fastLayer (bank 3 5).shape 179818 2360 5 1 1 1 0) (start := 0)
      [
      (128,3772071364902596559931104), (128,1960049842191485491451616),
      (115,503807676709892279957973)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel))

private theorem receipt_3_5_2360_1 : fastPhase (bank 3 5).shape 179818 2360 5 1 1 1 1 = 6198883295124127398952014 :=
  phase_of_block (n := 371) (by decide +kernel)
    (CompactRank6970.from_blocks (f := fastLayer (bank 3 5).shape 179818 2360 5 1 1 1 1) (start := 0)
      [
      (128,3756814924086543244447584), (128,1947321132987303367769952),
      (115,494747238050280786734478)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel))

theorem receipt_3_5 : Checked (bank 3 5) 5 1 1 := by
  refine checked_from_values (bank 3 5) 5 1 1
    (P3_7_1.checked (bank 3 5) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1696_370)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_3_5_2359_0 receipt_3_5_2359_1 receipt_3_5_2360_0 receipt_3_5_2360_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_0_6_2359_0 : fastPhase (bank 0 6).shape 179818 2359 7 1 0 1 0 = 100424248562057944154159344 :=
  phase_of_block (n := 381) (by decide +kernel)
    (CompactRank6970.from_blocks (f := fastLayer (bank 0 6).shape 179818 2359 7 1 0 1 0) (start := 0)
      [
      (128,58778265899368218944800036), (128,32070585476402042965846152),
      (125,9575397186287682243513156)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel))

private theorem receipt_0_6_2359_1 : fastPhase (bank 0 6).shape 179818 2359 7 1 0 1 1 = 99854675329364859233124210 :=
  phase_of_block (n := 381) (by decide +kernel)
    (CompactRank6970.from_blocks (f := fastLayer (bank 0 6).shape 179818 2359 7 1 0 1 1) (start := 0)
      [
      (128,58555046318472817367735556), (128,31880497311077722960511358),
      (125,9419131699814318904877296)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel))

private theorem receipt_0_6_2360_0 : fastPhase (bank 0 6).shape 179818 2360 7 1 0 1 0 = 100425014695149435211699218 :=
  phase_of_block (n := 381) (by decide +kernel)
    (CompactRank6970.from_blocks (f := fastLayer (bank 0 6).shape 179818 2360 7 1 0 1 0) (start := 0)
      [
      (128,58778769138807546556912188), (128,32070801342606573208886589),
      (125,9575444213735315445900441)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel))

private theorem receipt_0_6_2360_1 : fastPhase (bank 0 6).shape 179818 2360 7 1 0 1 1 = 99855438102047382108813777 :=
  phase_of_block (n := 381) (by decide +kernel)
    (CompactRank6970.from_blocks (f := fastLayer (bank 0 6).shape 179818 2360 7 1 0 1 1) (start := 0)
      [
      (128,58555547975204332776120651), (128,31880712073603128526025685),
      (125,9419178053239920806667441)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel))

theorem receipt_0_6 : Checked (bank 0 6) 7 0 1 := by
  refine checked_from_values (bank 0 6) 7 0 1
    (P3_7_1.checked (bank 0 6) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1817_380)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_0_6_2359_0 receipt_0_6_2359_1 receipt_0_6_2360_0 receipt_0_6_2360_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_1_6_2359_0 : fastPhase (bank 1 6).shape 179818 2359 7 1 0 2 0 = 90350562948123584274548521 :=
  phase_of_block (n := 381) (by decide +kernel)
    (CompactRank6970.from_blocks (f := fastLayer (bank 1 6).shape 179818 2359 7 1 0 2 0) (start := 0)
      [
      (128,52937648879691676095706978), (128,28823398774324243421282217),
      (125,8589515294107664757559326)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel))

private theorem receipt_1_6_2359_1 : fastPhase (bank 1 6).shape 179818 2359 7 1 0 2 1 = 89837078194980147626399553 :=
  phase_of_block (n := 381) (by decide +kernel)
    (CompactRank6970.from_blocks (f := fastLayer (bank 1 6).shape 179818 2359 7 1 0 2 1) (start := 0)
      [
      (128,52735740363500658437312661), (128,28652095102469098302510654),
      (125,8449242729010390886576238)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel))

private theorem receipt_1_6_2360_0 : fastPhase (bank 1 6).shape 179818 2360 7 1 0 2 0 = 90351252405529263749913201 :=
  phase_of_block (n := 381) (by decide +kernel)
    (CompactRank6970.from_blocks (f := fastLayer (bank 1 6).shape 179818 2360 7 1 0 2 0) (start := 0)
      [
      (128,52938102130268715999366561), (128,28823592793533402334666191),
      (125,8589557481727145415880449)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel))

private theorem receipt_1_6_2360_1 : fastPhase (bank 1 6).shape 179818 2360 7 1 0 2 1 = 89837764619168497832916036 :=
  phase_of_block (n := 381) (by decide +kernel)
    (CompactRank6970.from_blocks (f := fastLayer (bank 1 6).shape 179818 2360 7 1 0 2 1) (start := 0)
      [
      (128,52736192181128648261990610), (128,28652288126575244996795349),
      (125,8449284311464604574130077)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel))

theorem receipt_1_6 : Checked (bank 1 6) 7 0 2 := by
  refine checked_from_values (bank 1 6) 7 0 2
    (P3_7_1.checked (bank 1 6) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1817_380)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_1_6_2359_0 receipt_1_6_2359_1 receipt_1_6_2360_0 receipt_1_6_2360_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_2_6_2359_0 : fastPhase (bank 2 6).shape 179818 2359 7 1 0 7 0 = 48498445748702196839828992 :=
  phase_of_block (n := 381) (by decide +kernel)
    (CompactRank6970.from_blocks (f := fastLayer (bank 2 6).shape 179818 2359 7 1 0 7 0) (start := 0)
      [
      (128,28629467793418586293707200), (128,15355578352539634826314176),
      (125,4513399602743975719807616)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel))

private theorem receipt_2_6_2359_1 : fastPhase (bank 2 6).shape 179818 2359 7 1 0 7 1 = 48218773320373076228729116 :=
  phase_of_block (n := 381) (by decide +kernel)
    (CompactRank6970.from_blocks (f := fastLayer (bank 2 6).shape 179818 2359 7 1 0 7 1) (start := 0)
      [
      (128,28516908022037931471004608), (128,15262540231022923888272320),
      (125,4439325067312220869452188)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel))

private theorem receipt_2_6_2360_0 : fastPhase (bank 2 6).shape 179818 2360 7 1 0 7 0 = 48498814129078782478778998 :=
  phase_of_block (n := 381) (by decide +kernel)
    (CompactRank6970.from_blocks (f := fastLayer (bank 2 6).shape 179818 2360 7 1 0 7 0) (start := 0)
      [
      (128,28629710962350403279627712), (128,15355681388240244373382592),
      (125,4513421778488134825768694)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel))

private theorem receipt_2_6_2360_1 : fastPhase (bank 2 6).shape 179818 2360 7 1 0 7 1 = 48219140042615685524133331 :=
  phase_of_block (n := 381) (by decide +kernel)
    (CompactRank6970.from_blocks (f := fastLayer (bank 2 6).shape 179818 2360 7 1 0 7 1) (start := 0)
      [
      (128,28517150393462786507271424), (128,15262642726149990682512640),
      (125,4439346923002908334349267)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel))

theorem receipt_2_6 : Checked (bank 2 6) 7 0 7 := by
  refine checked_from_values (bank 2 6) 7 0 7
    (P3_7_1.checked (bank 2 6) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1809_380)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_2_6_2359_0 receipt_2_6_2359_1 receipt_2_6_2360_0 receipt_2_6_2360_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_3_6_2359_0 : fastPhase (bank 3 6).shape 179818 2359 7 1 1 1 0 = 10051312339914880601333415 :=
  phase_of_block (n := 396) (by decide +kernel)
    (CompactRank6970.from_blocks (f := fastLayer (bank 3 6).shape 179818 2359 7 1 1 1 0) (start := 0)
      [
      (128,5788116794601520380142176), (128,3194534712977282224460384),
      (128,1061025838957477080384096), (12,7634993378600916346759)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel))

private theorem receipt_3_6_2359_1 : fastPhase (bank 3 6).shape 179818 2359 7 1 1 1 1 = 9995367540917469027604551 :=
  phase_of_block (n := 396) (by decide +kernel)
    (CompactRank6970.from_blocks (f := fastLayer (bank 3 6).shape 179818 2359 7 1 1 1 1) (start := 0)
      [
      (128,5766428242309502563298016), (128,3176167982000869250824928),
      (128,1046316131669203746245344), (12,6455184937893467236263)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel))

private theorem receipt_3_6_2360_0 : fastPhase (bank 3 6).shape 179818 2360 7 1 1 1 0 = 10051378270726116260607957 :=
  phase_of_block (n := 396) (by decide +kernel)
    (CompactRank6970.from_blocks (f := fastLayer (bank 3 6).shape 179818 2360 7 1 1 1 0) (start := 0)
      [
      (128,5788163097407730963246624), (128,3194551397721287268285984),
      (128,1061028774489696743755296), (12,7635001107401285320053)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel))

private theorem receipt_3_6_2360_1 : fastPhase (bank 3 6).shape 179818 2360 7 1 1 1 1 = 9995433129171942461975097 :=
  phase_of_block (n := 396) (by decide +kernel)
    (CompactRank6970.from_blocks (f := fastLayer (bank 3 6).shape 179818 2360 7 1 1 1 1) (start := 0)
      [
      (128,5766474347727853174011936), (128,3176184561646410816563232),
      (128,1046319028298899745806368), (12,6455191498778725593561)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel))

theorem receipt_3_6 : Checked (bank 3 6) 7 1 1 := by
  refine checked_from_values (bank 3 6) 7 1 1
    (P3_7_1.checked (bank 3 6) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1809_395)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_3_6_2359_0 receipt_3_6_2359_1 receipt_3_6_2360_0 receipt_3_6_2360_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_0_7_2359_0 : fastPhase (bank 0 7).shape 179818 2359 10 1 0 1 0 = 293146671187404124951586956 :=
  phase_of_block (n := 481) (by decide +kernel)
    (CompactRank6970.from_blocks (f := fastLayer (bank 0 7).shape 179818 2359 10 1 0 1 0) (start := 0)
      [
      (128,142809870241073667244552192), (128,92173418804280466962296832),
      (128,47833151552411051739602178), (97,10330230589638939005135754)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel))

private theorem receipt_0_7_2359_1 : fastPhase (bank 0 7).shape 179818 2359 10 1 0 1 1 = 291828490479790534070068152 :=
  phase_of_block (n := 481) (by decide +kernel)
    (CompactRank6970.from_blocks (f := fastLayer (bank 0 7).shape 179818 2359 10 1 0 1 1) (start := 0)
      [
      (128,142393905028524072796386240), (128,91806581160278912173364160),
      (128,47512267842666746502357074), (97,10115736448320802597960678)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel))

private theorem receipt_0_7_2360_0 : fastPhase (bank 0 7).shape 179818 2360 10 1 0 1 0 = 293148889829540973236799382 :=
  phase_of_block (n := 481) (by decide +kernel)
    (CompactRank6970.from_blocks (f := fastLayer (bank 0 7).shape 179818 2360 10 1 0 1 0) (start := 0)
      [
      (128,142811103302212485174998112), (128,92174085391381525430731872),
      (128,47833425687563811580675164), (97,10330275448383151050394234)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel))

private theorem receipt_0_7_2360_1 : fastPhase (bank 0 7).shape 179818 2360 10 1 0 1 1 = 291830701399773617464244450 :=
  phase_of_block (n := 481) (by decide +kernel)
    (CompactRank6970.from_blocks (f := fastLayer (bank 0 7).shape 179818 2360 10 1 0 1 1) (start := 0)
      [
      (128,142395135120196347349622880), (128,91807245479331760716435552),
      (128,47512540345106659147471371), (97,10115780455138850250714647)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel))

theorem receipt_0_7 : Checked (bank 0 7) 10 0 1 := by
  refine checked_from_values (bank 0 7) 10 0 1
    (P3_7_1.checked (bank 0 7) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_2285_480)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_0_7_2359_0 receipt_0_7_2359_1 receipt_0_7_2360_0 receipt_0_7_2360_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_1_7_2359_0 : fastPhase (bank 1 7).shape 179818 2359 10 1 0 2 0 = 263309146915138806703823653 :=
  phase_of_block (n := 481) (by decide +kernel)
    (CompactRank6970.from_blocks (f := fastLayer (bank 1 7).shape 179818 2359 10 1 0 2 0) (start := 0)
      [
      (128,128461283632278458491329952), (128,82748632099019896430366112),
      (128,42858631393028760777528324), (97,9240599790811691004599265)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel))

private theorem receipt_1_7_2359_1 : fastPhase (bank 1 7).shape 179818 2359 10 1 0 2 1 = 262122283928871151699866754 :=
  phase_of_block (n := 481) (by decide +kernel)
    (CompactRank6970.from_blocks (f := fastLayer (bank 1 7).shape 179818 2359 10 1 0 2 1) (start := 0)
      [
      (128,128085128652927786976634080), (128,82418035054340932081792224),
      (128,42570485570570767434587358), (97,9048634651031665206853092)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel))

private theorem receipt_1_7_2360_0 : fastPhase (bank 1 7).shape 179818 2360 10 1 0 2 0 = 263311140328530904353994278 :=
  phase_of_block (n := 481) (by decide +kernel)
    (CompactRank6970.from_blocks (f := fastLayer (bank 1 7).shape 179818 2360 10 1 0 2 0) (start := 0)
      [
      (128,128462392832479601054096832), (128,82749230547247565324893632),
      (128,42858877029893786241274803), (97,9240639918909951733729011)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel))

private theorem receipt_1_7_2360_1 : fastPhase (bank 1 7).shape 179818 2360 10 1 0 2 1 = 262124270379388737999031854 :=
  phase_of_block (n := 481) (by decide +kernel)
    (CompactRank6970.from_blocks (f := fastLayer (bank 1 7).shape 179818 2360 10 1 0 2 1) (start := 0)
      [
      (128,128086235164802937714239040), (128,82418631457170668296652352),
      (128,42570729740809664015894544), (97,9048674016605467972245918)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel))

theorem receipt_1_7 : Checked (bank 1 7) 10 0 2 := by
  refine checked_from_values (bank 1 7) 10 0 2
    (P3_7_1.checked (bank 1 7) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_2285_480)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_1_7_2359_0 receipt_1_7_2359_1 receipt_1_7_2360_0 receipt_1_7_2360_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_2_7_2359_0 : fastPhase (bank 2 7).shape 179818 2359 10 1 0 7 0 = 139018141037022638832256640 :=
  phase_of_block (n := 481) (by decide +kernel)
    (CompactRank6970.from_blocks (f := fastLayer (bank 2 7).shape 179818 2359 10 1 0 7 0) (start := 0)
      [
      (128,68539217503527077618691360), (128,43521965885755780545305888),
      (128,22223452260932670215682314), (97,4733505386807110452577078)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel))

private theorem receipt_2_7_2359_1 : fastPhase (bank 2 7).shape 179818 2359 10 1 0 7 1 = 138380571788675020668060313 :=
  phase_of_block (n := 481) (by decide +kernel)
    (CompactRank6970.from_blocks (f := fastLayer (bank 2 7).shape 179818 2359 10 1 0 7 1) (start := 0)
      [
      (128,68330893607180597065150816), (128,43343235575041423126864224),
      (128,22071633893156426184518085), (97,4634808713296574291527188)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel))

private theorem receipt_2_7_2360_0 : fastPhase (bank 2 7).shape 179818 2360 10 1 0 7 0 = 139019195754816313788667117 :=
  phase_of_block (n := 481) (by decide +kernel)
    (CompactRank6970.from_blocks (f := fastLayer (bank 2 7).shape 179818 2360 10 1 0 7 0) (start := 0)
      [
      (128,68539809417051430252196160), (128,43522280718598668194459968),
      (128,22223579672752552229698135), (97,4733525946413663112312854)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel))

private theorem receipt_2_7_2360_1 : fastPhase (bank 2 7).shape 179818 2360 10 1 0 7 1 = 138381622727780843415210994 :=
  phase_of_block (n := 481) (by decide +kernel)
    (CompactRank6970.from_blocks (f := fastLayer (bank 2 7).shape 179818 2360 10 1 0 7 1) (start := 0)
      [
      (128,68331484020147577127819648), (128,43343549296689935146039680),
      (128,22071760530381336754255775), (97,4634828880561994387095891)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel))

theorem receipt_2_7 : Checked (bank 2 7) 10 0 7 := by
  refine checked_from_values (bank 2 7) 10 0 7
    (P3_7_1.checked (bank 2 7) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_2285_480)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_2_7_2359_0 receipt_2_7_2359_1 receipt_2_7_2360_0 receipt_2_7_2360_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_3_7_2359_0 : fastPhase (bank 3 7).shape 179818 2359 10 1 1 1 0 = 36114180695300802153943075 :=
  phase_of_block (n := 499) (by decide +kernel)
    (CompactRank6970.from_blocks (f := fastLayer (bank 3 7).shape 179818 2359 10 1 1 1 0) (start := 0)
      [
      (128,17322618370408446801647392), (128,11244206499958642587551520),
      (128,5971267114922924700071712), (115,1576088710010788064672451)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel))

private theorem receipt_3_7_2359_1 : fastPhase (bank 3 7).shape 179818 2359 10 1 1 1 1 = 35954562133988071239071850 :=
  phase_of_block (n := 499) (by decide +kernel)
    (CompactRank6970.from_blocks (f := fastLayer (bank 3 7).shape 179818 2359 10 1 1 1 1) (start := 0)
      [
      (128,17272759068906282993359136), (128,11200200051333472347777312),
      (128,5933588191357737920117024), (115,1548014822390577977818378)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel))

private theorem receipt_3_7_2360_0 : fastPhase (bank 3 7).shape 179818 2360 10 1 1 1 0 = 36114417236426962794405300 :=
  phase_of_block (n := 499) (by decide +kernel)
    (CompactRank6970.from_blocks (f := fastLayer (bank 3 7).shape 179818 2360 10 1 1 1 0) (start := 0)
      [
      (128,17322761099788718566802688), (128,11244273890066665997149440),
      (128,5971290264312235024336128), (115,1576091982259343206117044)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel))

private theorem receipt_3_7_2360_1 : fastPhase (bank 3 7).shape 179818 2360 10 1 1 1 1 = 35954797699239599467664805 :=
  phase_of_block (n := 499) (by decide +kernel)
    (CompactRank6970.from_blocks (f := fastLayer (bank 3 7).shape 179818 2360 10 1 1 1 1) (start := 0)
      [
      (128,17272901328028966613256768), (128,11200267146557133811771968),
      (128,5933611183736160443910720), (115,1548018040917338598725349)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel))

theorem receipt_3_7 : Checked (bank 3 7) 10 1 1 := by
  refine checked_from_values (bank 3 7) 10 1 1
    (P3_7_1.checked (bank 3 7) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_2285_498)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_3_7_2359_0 receipt_3_7_2359_1 receipt_3_7_2360_0 receipt_3_7_2360_1 (by decide +kernel) (by decide +kernel)

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

theorem group2_avoids {h : ℕ} {D : K1_14_1.PoleData h} (Crt : K1_14_1.CRTLift D)
    (word : K1.I → K1_14.L) (lo : 2359 ≤ h) (hi : h ≤ 33579) (rect : Fin 4)
    (i : Fin 3) {G : K1_14.Jet} (irr : Irreducible G) (seeded : K1_14_2.UsesSeed G)
    (slope : 1≤G.natDegree) (hs : seed rect≤K1_14_2_2_2_1.seedDegree G)
    (hj : G.natDegree+excess rect≤K1_14_2_2_2_1.jetDegree G) :
    ∃ Q ∈ K1_14_1.evaluated Crt word (bank rect (group2_stage i)).shape
      (cutoff h rect (group2_stage i)), ¬ G∣Q :=
  (group2_checked rect i).avoids Crt word lo hi irr seeded slope hs hj

end Lower6960.RescueSource
