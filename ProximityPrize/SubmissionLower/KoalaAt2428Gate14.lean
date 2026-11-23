import ProximityPrize.SubmissionLower.KoalaAt2428Gate12
import ProximityPrize.SubmissionLower.KoalaGateSharedData
import ProximityPrize.SubmissionLower.KoalaGateChunkSums
import ProximityPrize.SubmissionLower.KoalaSplitGateWords

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000

set_option linter.defProp false

namespace KoalaAt2428Gate14
open KoalaGateSharedData
open FadicGate KoalaGateCheck
open KoalaWeightedRate (Envelope)
open KoalaFarBridge (rowCheck plainCheck)

def envelope : Envelope :=
  ⟨136,56,14,136,56,3536,4436,⟨2651005096464291840,14259500844614503680,3147971320526995200⟩,1154562859954099031040⟩
abbrev split:ℕ:=96
abbrev unit:ℕ:=499354621755067522560
abbrev terminal:ℕ:=72
abbrev gate:=KoalaSplitRow.rate envelope split unit

private def boxesTape : List (List Entry) := [
  unpack 1 0xfdeb0f9,unpack 2 0x494d96c11e56c72,unpack 2 0x48ccd8413ebfca0,unpack 3 0x4a8bdc2494dd5215f27e5e,unpack 4 0x498eddc4b4e94248cb9ba17a2ad55,unpack 4 0x494c9d24b4dd6448cc98e19a95a60,unpack 5 0x4a509d24b4ddae498e18e484b5a41b598957,unpack 6 0x4a105e04b4d994494e1d84b0cd9248ccd601d603662,
  unpack 6 0x498edb84b4e1c6490f55e4b8bdb8484b99a1f106559,unpack 7 0x4a925f0490dde84bd0d70490d1be4b8d578488bd8c216d56bd,unpack 8 0x4a0957e4a92a0a495096e4c0e9ce494e9a04b0bdbc488d942231dcddd,unpack 8 0x4bcfd78494dde44a125d04b8d1cc48cd5924b8f12c488adb6252432be,unpack 8 0x4cd41d8490cdca494fdb24b8d59e48ced644c0c9a4484c578272adfc9,unpack 9 0x48cb1864d12e0c494fdd6490e97e4bcd9b4488ddc64b8c97448cc96a293144ab,unpack 9 0x480a1704d945ea490f9d44c4f574490f1ae48cc9d84b8cd6a484e5122ae220c9,unpack 10 0x4d135f2490f1b04c10d82494ee0249d09e64b8cd8e48ce1964c0ed0e480b5a42ce885b2,
  unpack 10 0x4b8dd7a4a136144b8c16449905e44950dac4bccdae48ce58c4b8d552488b9982eeedc26,unpack 11 0x4c1aab84b0c4f24a932864c4f16e490f5ee488e58e4c0d1c648ce95c4bcbd92480bd90309efcae,unpack 11 0x4d961f848099844a54a5c4c909bc494e5ba484f14c4c4e9a6484b5de4c4dd46480c18632a5b827,unpack 12 0x4d5cef2490f9c84c4e9a649519fa4ccf9e4490fd904c8ed9c480c1ce488d98a4bce526480a1dc3455d8b0,unpack 13 0x49d09c84c9cade47ca95c4d5262048901324ccfde848cce1648cf1b24c8f16c480e54a4c0a9c4480c57c365c9429,unpack 14 0x47c99464b56a5c4b16e724b0a93c4b1820847895a44d511e8484ddca488edd44cd0520484bdd64c4cd6247cadbe3862ea9c,unpack 15 0x47c89724788d6a4cddabc49d121a47cad504e56a3a488e9964cce1a448d0a04488e1744c4cdaa480c9ba4c4cd6247cc9603a1361b3,unpack 15 0x4749162498fdd44cdd6d847cc178488e5d64dd29fc49519f84cce170485018c4ccc5e0484e960480d1a44c0d92047cb5a83c1a4881,
  unpack 16 0x478a918478a5224b552944b9aa5c4748dac49d32204ccf18e4951dee4cce5ae480d5bc488e5b24c8d592480d5764c8d154478b9a03e208217,unpack 16 0x474ad0a478896c4cdc30e4a13636478ad544ad7e6c4bcccfa495023a4d0e9c4480e5824c8d9ac484fd60480b5ee4c8bd66478bd963fd0b10e,unpack 17 0x4709146474954a49501cc4cdd6d8484e1be478ad604ad827a4bcad40491162e4d4eda0484f19447cf9704d4dd86480b9e64c4c15e478bd9641d75e19,unpack 17 0x470953a470896c4b56e4a4c5beb0474c918484e5e4499227e4d0ed72484edb24d4f5b2488f5f447cd97e4ccc99e480e1784c8c55247cc18844344f7d,unpack 18 0x47cc18a46c953c47091564d5d6d24a96a44474ad624952e3c48d05c64dd15b8478e1324d4d202484f5f6480e19e4cccd8047cdd744ccd92a4749dee458e3a1a,unpack 18 0x46c953c6889d2427515944d1dec0490ee4246c9d924ad8a4c474ada24e531ce47cd1ca4d8f994478cdc6480e5924d0d5a0478f5224d0a1ae474c5704794e71c,unpack 19 0x490fdc2464914846c953a4b17a284c9c300478bd82470a1784a98e90474b5624e51e0648501d64d0d58e47ce58247cfd544d4ae0047cd18a4cccd3a474b5ac499b5a75,unpack 19 0x460953c6bc953c210895e4d5d6ce4b58e86468a17c484f9a449d71e047085e84e935cc480ee064d8f16247cd990480edc64ccbd88478d1964cce900478a1e04ba20780,
  unpack 20 0x4a12e1e4649930460914848cfdc44d1d2de495361646cc9104951a6448915e647ce1c44e101a0480f5f84d9052c480ca26478dd884ccbd9a47cdd744ccb95c478bda84da86c62,unpack 20 0x470c57045c953e46091464ad6a364d5dece470f17046c85c64a98264470c9c248d19fe4d0d1504811d8c4dcbdec480f5b0478ddac4d4f11c478b1da4d0c156474b9a44faf196d,unpack 21 0x4bd6e4e450913845c954c46499344d1d2ce4b9ba7a468b55646889c04b1aaaa468a58648d59bc4d48daa4850dda4d8e17a47ce9e447ce17c4d0cda2474bda04d4c95c470b9885108f58d,unpack 21 0x47cf9b4454954c45c914c48905b44cdd6c049d5240464ad60478e1ea4a16e56468ad8248d361e4dcdd72478d9b64e91194470bde4478e98c4d8cd7a474c99c4d0c54c474c582536603dd,unpack 22 0x4d9a696448993045095404548d5a4b176264c9d2ce478f9bc468a97848d322a4894dbc46c89e048d3a144e509ac470c5c64e4f57c474d5a0474cdbc4dcd97446cf50e4dca1c246cadc855162465,unpack 22 0x491320a444953e44c915045c9d2e4d1dab64c1c6cc45ca966464d0fe4994700478edc8478ddbe4851dd44e4f5c847cf99c4d8c9a847cf19a470c1b44d8d564474d1864d4b57446cc17656c68d08,unpack 23 0x8c1b698068bd827b099380d889584850dac4cdd6c24a16e5845cd4ec45c79f24b5c2d2460a566485122a470ddb04ed3926478ba564d8cd68480f59e46cf9444d89dde47cdd7e4d0b96c46cb1be58cd0067,unpack 23 0xb9821042c9542440993a44895444a96a464c9dab047d19de454ad50478e1fa4a1826a460a99048d463c468ad824e901be478e9d64e0e558478e5bc474ddae4d8c56c470c1b44dcd51a468e9285ad4777e,
  unpack 24 0x4fd96340213db842c79a643c915044495364cdd2c64c1d2c645cc56645ca18c4893a1648969ba46081fc4914e244609db24f115a8474e9ba4e50d08474b63e474e59a4dcc95e470c1b44d0b558474c1ac5cda1253,unpack 24 0x2853ec9dde034a51847501b68c1a34a0adc5e48405e2c069007449d6aac471258046485f0489424a474e98e4e8e57a470ddfa4ed058c464b9b447ced9c4dd00ec46c92124dcc150468b5965e8a7af5,unpack 24 0x14280272f921a48ab250b719262ff1f0144c79de454d0fe4b1c6ca4649a0446ce5c247d161247901ec4dce0ea478ca2a4ecf1a046cd9be470d5a24e0d146470c99e4d8c54846cc19260e78946,unpack 24 0x1428129ee0412291306d12ec470a12d05004d95e468f1c64a1ba3e45889ea47d1dfa470edb2479061a4e4a9d4474e9d84e4d18c471112646ca6264e4d14446ccd964d8b17c46cc1926297a9ce,unpack 24 0x50a14084f6fa384f93828501d25b047d4de448d3a7e45ce916485620845c665a47d19e24f0f58e46caa464e504dc470b22846cc5d04e0d56046cb9a64dccd30470c58464f49b32,unpack 24 0x2850a142850a142850152d744853a98468bd584f109ec470ce1c470f59e4e0c588474b2284e0c980471110246486384d8ad68470d184664e85d0,unpack 24 0x2850a142850a142854813dee13d3e1e35531504fd05d446d0d9e46cb22c4e4960446cae40470d5c24e4d53e46cc99c4d8b966470cd7068ab7734,unpack 24 0xa142850a142850a1428513d3e063f9220646531284e0aa24479290c4647eaa46cd5ac4e095ea46cc1924dcbd5a464f1146a063a4c,
  unpack 24 0x50a142850a142850a142851c93e063893e0644131244f4d9b4464ae164e8a1e246c963245ca5c84e8d908464b9ac6c0c005e,unpack 24 0x142850a142850a142850a142850f93e064a1213646cf17a4e48a32468a9f046ccd9e4d87206468b9aa6e1273be,unpack 24 0xa142850a142850a142850a142851713e0643125244e0c584468a62a4648e1e4e085d4468c5a870192f37,unpack 24 0x50a142850a142850a142850a142851813e06499190c468cd96464a60c4e06618464c59471ca36a9,unpack 24 0x2850a142850a142850a142850a142851a93e0647d00fa4d8cd7446886124608e227427280c,unpack 24 0x2850a142850a142850a142850a142854813dfe1b9320c4e8f4de454c56e474960a77314f54,unpack 24 0x142850a142850a142850a142850a142854813e002313d62468d542464cd7e78e29080,unpack 24 0xa142850a142850a142850a142850a142854813dd42353142458c9867a3ca668,
  unpack 24 0x50a142850a142850a142850a142850a142853ad3d8a2f921667c435371,unpack 24 0x50a142850a142850a142850a142850a142854813e0437d356a9939b93c]
def boxes (r : ℕ) : List FadicGate.Entry :=
  if r < 14 then [] else boxesTape.getD (r-14) []

def plain : ℕ → ℕ × ℕ × ℕ
  | _ => (0,0,0)

private def powersTape : List String := [
  "","","","","","","","",
  "","","","","","","!$","!$",
  "!$'","!$'.","!$'+","!#',5","!#&,09","!#&*06","!#&*17C","!#&+28EC",
  "!#&).9?E","!#&).59G","!#%*/3;II",z5A,"!#%),5=EKX",z4j,"!#%(-19>OMi",z6B,
  "!#%(+17@KQXy","!#%',28AESQqy","!#%(,38CAUSi}y",z6l,"!#$'*/59DPWXy~#$}",z6U,z6F,z5s,
  "!#$'*-5<BGV]Zy~#0~#,~#(",z5i,z3v,"!#$&*.26>KIca`~#$~#8~#4~#0~#%",z5U,z4v,z3l,"!#$&*-38A@NMige~##~#C~#@~#;~#8~#%",
  "!#$&)-09=AONcigx~#;~#C~#@~#;~#1",z4Z,z3U,"!#$&),14:CGQPomk~##~#C~#K~#G~#C~#=~#%",z3S,z4L,z4K,(zz68 ++ "#W~#S~#I~#9~#*"),
  (zz104 ++ "ro~#;~#[~#W~#I~#9~#*"),"!#$%(+/26=GFWViwrl~#)~#S~#X~#I~#9~#*","!#$%(+/27=HGXV`xrls~#A~#X~#I~#9~#*","!#$%(+037>HGZVUxrlf~#-~#X~#I~#9~#*","!#$%'*-38>DGSVSnrlfw~#E~#I~#9~#*","!#$%'*-38??GLVSdrlfd~#1~#I~#9~#*","!##%'*.48?=GEVSYrlf`{~#I~#9~#*","!#$%(*.18:=GEVSPrlf`h~#5~#9~#*",
  "!##%'+.057=GEVSPhlf`Z~#!~#9~#*","!##%').037=GEPSP^lf`Zl~#9~#*","!##%'),037=BEISPSlf`ZW~#&~#*","!##%'),037==ECSPMlf`ZTp~#*",(zz82 ++ "Mbf`ZT[~#*"),(zz82 ++ "MWf`ZTNt"),"!##%'(,-379<ECMPMMf`ZTN`"]

def powers (r : ℕ) : List ℕ :=
  if r=0 then [] else KoalaSplitGateWords.powers (powersTape.getD (r-1) "")

def plainPowers : ℕ → List ℕ
  | _ => []

def tailPowers : List ℕ := KoalaSplitGateWords.powers "!##%'(,-376<ECFPMJf`ZTNLwhXH9*"

def priced (r:ℕ):Bool:=rowCheck gate r (boxes r) (powers r) (plain r) (plainPowers r)
private theorem priced_list : (List.range 71).all (fun i => priced (i+1)) = true := by decide +kernel

theorem prices {r : ℕ} (hr : 0 < r) (hR : r < terminal) : priced r = true :=
  price hr hR priced_list

theorem tail:plainCheck gate terminal (4012,1650,550) tailPowers=true:=by decide +kernel

private theorem exactLoss0 : lossChunk 1 envelope plain boxes 0 24 = 9727784053236 :=
  by decide +kernel

private theorem exactLoss24 : lossChunk 1 envelope plain boxes 24 24 = 8466260929136 :=
  by decide +kernel

private theorem exactLoss48 : lossChunk 1 envelope plain boxes 48 23 = 2558343780484 :=
  by decide +kernel

theorem loss_bound (N : ℕ) : Bound envelope terminal plain boxes 20752388762856 N :=
  loss_of_chunks 1 envelope terminal plain boxes 20752388762856 N (by decide) (by decide)
    (LossSum.empty _ _ _ _
      |>.append 24 9727784053236 exactLoss0
      |>.append 24 8466260929136 exactLoss24
      |>.append 23 2558343780484 exactLoss48)

def receipt : KoalaSplitProof.Receipt envelope split unit :=
  ⟨terminal, plain, boxes, powers, plainPowers, tailPowers, 20752388762856,
    by decide,by decide,loss_bound,fun _ h h' => prices h h', tail⟩

end KoalaAt2428Gate14

#print axioms KoalaAt2428Gate14.loss_bound
#print axioms KoalaAt2428Gate14.receipt
