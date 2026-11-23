import ProximityPrize.SubmissionLower.KoalaAt2428Gate14
import ProximityPrize.SubmissionLower.KoalaGateSharedData
import ProximityPrize.SubmissionLower.KoalaGateChunkSums
import ProximityPrize.SubmissionLower.KoalaSplitGateWords

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000

set_option linter.defProp false

namespace KoalaAt2428Gate15
open KoalaGateSharedData
open FadicGate KoalaGateCheck
open KoalaWeightedRate (Envelope)
open KoalaFarBridge (rowCheck plainCheck)

def envelope : Envelope :=
  ⟨136,56,13,136,56,3536,4436,⟨2617010426141989440,13752360810808068960,4703386092268601760⟩,1138612163609219450400⟩
abbrev split:ℕ:=96
abbrev unit:ℕ:=497647107915490404480
abbrev terminal:ℕ:=72
abbrev gate:=KoalaSplitRow.rate envelope split unit

private def boxesTape : List (List Entry) := [
  unpack 1 0x13957e97,unpack 2 0x494e15015f2f1e8,unpack 2 0x48cc99417a2ad6a,unpack 3 0x4b4dd6248ccd8c19a9dc5b,unpack 4 0x4b4bdfe498e194484d9481b5a0b51,unpack 5 0x4b4d98e495057e4b0cd9048cd15c1d60c6ce,unpack 5 0x4b10160494c1fc4b8d17c484e1341f10f5c4,unpack 6 0x490ddec4bd1d3e490c1f24b8fd08488c18a216df59a,
  unpack 6 0x494f9a24c0d5fe494e9a64b0e54a488c57e231e1621,unpack 7 0x494f5ac4a0fe404b8f95848cd9904b8d96a48495ee24cdee7a,unpack 7 0x490e19a49529444b4a60a494ddb04bcdd5a480c17e26d49b86,unpack 8 0x4d12e04494fdde490e9844bd0536488e1c64b899ee48cc970293144ca,unpack 9 0x480a56c4d91a58494fdde4c0f168490d9f848ce19e4b8fce248499e62ae1bbe3,unpack 9 0x494f5bc4c5254a494da3c49905ea4b8fd0648ce5944c09dda480b5b02ce820ce,unpack 10 0x4b8dd764a10a8e4b8c15e499356a49511aa4bc9a3248ce5924b8ed0e488a1de2eeedc49,unpack 10 0x4b0ad2e4a979ca4c4c1e6490f5f6488e5984c1053448ced584bc861e480bd9a309efcd2,
  unpack 11 0x4d94a30480e0ce4a91ee44c93934490e5b6484d9944c4e5a6488d9924c0d940480c58432a690c9,unpack 11 0x48cf9c24c8ba2a4951a024ccf9da490fd9a4c8ed90480f946488dd864bcc17a4808a283455d8d6,unpack 11 0x47ca9664d52614488e5884cd315648cedc848cf5b04c4b1fe484c9ac4c104c8480c97a365d7b3c,unpack 12 0x4b16e764b0d8b44b16a504787dee4d511dc484ddd448cf1e04c8e1684851ce24c4c96047cb1bc3863d1ae,unpack 12 0x49d459447c79e84e56a2c48ceda44c8dd9648d4570488e5724c4c9a8480cdb84c48e0448110be3a6a9b9a,unpack 13 0x4cdd6da480fcf2488e9d44d921f84951df64ccdd6e484e5e04cce188484b20448114fa4c0b17e47cb9a83c1abc21,unpack 14 0x4b13aca4bdc62647475f649d32284ccf1824951df64cce5a247cd1c648d2d0c4c8d190480d9724c88e00474fcea3dcb41aa,unpack 14 0x4cdc30e4a169b0474b14c4b147144bce8a849525e24d0e5c2484ed844c8d5aa4809a6a48120dc4c8b964478c1923fd1b502,
  unpack 15 0x49501d44ce0a52484e5bc47876004adc1d84c071e248d12344d528f0484f990480ddd64d0d5804809a424c4c152478bda241d75e47,unpack 16 0x470b8f44b53ece4c5f22a4747602484e5f049942324cd28ba48cf9b84d0edae488f9f24809a424c8c58e4812cbc4c8c14e47c7a5244344fac,unpack 17 0x46cc0c247095544d5a75a4a96a4a474e8d0495323c48d09c44dd11b64787e464d4f596484f6024812ce04ccc97e4809a424c8f4c44747e50458e3a4b,unpack 18 0x46c953c6889d28274f5ee4d2123a49111ea46ca1904ad4ef6474adae4e531c047915164dcb64847d19184809e5c4cd18cc478d58c4d07a04478c98247eb2bb0,unpack 18 0x464914a46c953c4ad76284d1fe7e4748614470e0de4a94f42474b56e4e5614448505d44d0d18c480a64847d24fa4d0cd8c47cd5884cc7e02474b5ba499b5aa8,unpack 19 0x46095406bc953c210b8d84d5d6ce4b592844686e18485390449d5240470664a4e935bc480ee144d4ed4e48128d8480a29c4cd08ae478866e4c9089247cd56e4ba336c8,unpack 19 0x4649932460914a48cfdc24d2025649506a446ce0de49502b048915f2478ddce4e148d2484b2c64d924ca480f5b8478e5864cc6a68478d97c4d510824746a864da86c97,unpack 20 0x474c97445c954046091464b16e324d1daca471054a468ad5e4ad4718471111048cd2ca4d0d14247d412e4e0e184480fdac4788e8e4d514ac4788e484d0c14847510c64fb05726,
  unpack 20 0x454953c458914a46499364d1d2c24bdbe80464c52c468b55a4b1aea846c664e48d81624d0ad3648511d84dce17e47496b04813ca64d0c9a0478c9a24d0bd544746e7a515f489b,unpack 21 0x480fdba450914a45c914e48501ae4d1dab649d85bc464b55e478e5e84a12f0e468f8c648ceaf64dd28964788e904e9118246cb9ec47ceda04d9208a474768a4d1185a474cd8053675008,unpack 21 0x448993245095404548d5c4b1761e4c9d2c247cfdc8464e0e448cf6d84896d7846c6a4048d8d444e4b6784751cfc4e0ed72474868047930de4d8765047128ae4d8c53a46cb1c65517708f,unpack 22 0x491320e444954044c915245c9d304cdd6a64c5cac445ce0e04606e0c4a1b9f2478aa8c47528f4484ceb44e544e4478a6784dd1cc847ca27c4711ccc4d8d1624747a7e4d50c78470d178571e3a7b,unpack 22 0x68bd847b0993a0dc8d5c48109a64cdd6b44a16e5245ce4d045ca9824b5c6d4460ad62484c70047134d84ecb6724793d064dc7a4447d48bc46cd1c24dc764e47934884d0b56a46cb5bc58ce5b02,unpack 23 0xb9a5b042c65d4440993a44895484a96a3c4c5d6a24811ddc458b1644751d5a4a14320460f4d648cfb16468ad924e954ce47896c24e1386847892a8474ddbe4d9206847066b64dcd50846918be5ad524ee,unpack 23 0x213db842c79da43c9152448993a4c9ceb64c5d6bc45cc566458d8fa4893e14489462e460b584490ff04460f8d04f10da6478f9bc4e07a6647540d8474ed964dc665447124ba4d0525047524ae5cdb7b5f,unpack 23 0x53ecadde034954e470fdb08c5b71a0ade5748403a9c068f4a249daa0a47101f4464b978484ef28478eda44e534784748ef64ed5c924686ab2479489a4dcc97446c66944dd203e46cc59a5ee2454b,
  unpack 23 0x28048ec42182cfc250b71526305070144c6dfc454a5864b20624464cd8a46cedc047d1e10474a6e24e10c7247901a64ece99c46ce1be47076b04e0d134471309a4d85e4a468b99a609136af,unpack 23 0x28129ee0412331306d0aec4709f2d05004e55e468f5c64a1c23e45891ea47d25fa470edb24790e1a4e4d150474f1d64e4727a470ddc246cd9aa4e5342a46c6aae4d9146246cc98e62992fbe,unpack 23 0xa14084f6fa384f93828501d31b047d49e448d327e45d0916485660845c6e5a47919dc4f4f59446ce1bc4e4c966470ed9a46c62e84e1384246cc1a64dc623a471307464f62121,unpack 23 0x50a142850a142850153d744852a984691cd04f101ea470a2a6470f99e4e0c188474e9984dcbd764707aa4468c5ba4dd1c4a46cd17a66501a31,unpack 23 0x50a142850a142854813dee13d3e1e3553d504fd1dd446d159e4687eb04e8c980470f1b446cd1b84e8d942468c9924d8b166470d56c68ad0b94,unpack 23 0x142850a142850a1428513d3e063f9220646559284e0dd9047d01a64607ea446cd9ac4e0c54e46cc9904dcb958464bdb46a0704a4,unpack 23 0xa142850a142850a142851c93e063893e06440fa064f53cd2464ed7c4e8627c46cd594460b5ce4e8d104464c1aa6c63f607,unpack 23 0x2850a142850a142850a142850f93e064a13d3646d0d7a4e4b992468769046cd19e4d8a960468bda86e14168e,
  unpack 24 0xa142850a142850a142850a142851713e064353d2c4d8d57446cf18c46456c44e4c132464c5a0701ae07a,unpack 24 0x50a142850a142850a142850a142851813e064993d0c468e196464e9624e01ec2464c99471cb0101,unpack 24 0x2850a142850a142850a142850a142852f13d763393d924d4c16c468cd6246052d2742800d8,unpack 24 0x2850a142850a142850a142850a142854813dfe319315e389258c454cd6e474dd5477331d79,unpack 24 0x142850a142850a142850a142850a142854813e002313d624690d42464d17e78e3694c,unpack 24 0xa142850a142850a142850a142850a142854813dd42353d42458fd867a3d8da8,unpack 24 0x50a142850a142850a142850a142850a142853d53d8a2d13d667c43b89d,unpack 24 0x50a142850a142850a142850a142850a142854813e043cd356a9ff5efac]
def boxes (r : ℕ) : List FadicGate.Entry :=
  if r < 16 then [] else boxesTape.getD (r-16) []

def plain : ℕ → ℕ × ℕ × ℕ
  | _ => (0,0,0)

private def powersTape : List String := [
  "","","","","","","","",
  "","","","","","","","",
  "!$","!$","!$'","!#',","!#&,0","!#&*0",z4F,"!#&+28",
  "!#&).9?","!#&).59","!#%*/3;I",z5A,"!#%),5=EK",z4j,z4i,z6B,
  z4S,z4R,"!#%(,38CAUSi",z4N,"!#$'*/59DQWXy","!#%'+04:EKYWq~#(","!#$'+04;FEZYi~#,","!#$'+05;GF]Za~#$~#,",
  z6T,z63,z3v,"!#$&*.26>KIcaa~##~#8~#4~#0","!#$')/27>LK]cax~#<~#8~#4~#0",z5R,z3l,z2v,
  z3f,z2t,z3U,"!#$&),14:CGQPomk~##~#C~#K~#G~#C~#=",z3S,(zz69 ++ "#O~#K~#F~#8"),(zz67 ++ "#S~#O~#H~#8"),(zz68 ++ "#W~#S~#H~#8"),
  (zz104 ++ "ro~#;~#[~#V~#H~#8"),"!#$%(+/26=GFWVhwrl~#)~#R~#W~#H~#8","!#$%(+/27=HGXV`wrls~#@~#W~#H~#8","!#$%(+037>HGYVUwrlf~#-~#W~#H~#8","!#$%'*-37>DGSVSnrlfw~#D~#H~#8","!#$%'*-38??GLVSdrlfc~#1~#H~#8","!##%'*.38?=GEVSYrlf`z~#H~#8","!#$%(*.18:=GEVSPrlf`g~#5~#8~#)",
  "!##%'+.057=GEVSPhlf`Y~!~~#8~#)","!##%').037=GEPSP^lf`Yk~#8~#)","!##%'),037=BEISPSlf`YW~#%~#)","!##%'),037==ECSPMlf`YTo~#)",(zz82 ++ "Mbf`YT[~#)"),(zz82 ++ "MWf`YTNs"),"!##%'(,-379<ECMPMMf`YTN`"]

def powers (r : ℕ) : List ℕ :=
  if r=0 then [] else KoalaSplitGateWords.powers (powersTape.getD (r-1) "")

def plainPowers : ℕ → List ℕ
  | _ => []

def tailPowers : List ℕ := KoalaSplitGateWords.powers "!##%'(,-376<ECFPMJf`YTNLwhWH9*"

def priced (r:ℕ):Bool:=rowCheck gate r (boxes r) (powers r) (plain r) (plainPowers r)
private theorem priced_list : (List.range 71).all (fun i => priced (i+1)) = true := by decide +kernel

theorem prices {r : ℕ} (hr : 0 < r) (hR : r < terminal) : priced r = true :=
  price hr hR priced_list

theorem tail:plainCheck gate terminal (4012,1650,550) tailPowers=true:=by decide +kernel

private theorem exactLoss0 : lossChunk 1 envelope plain boxes 0 24 = 9732346388059 :=
  by decide +kernel

private theorem exactLoss24 : lossChunk 1 envelope plain boxes 24 24 = 8453198788453 :=
  by decide +kernel

private theorem exactLoss48 : lossChunk 1 envelope plain boxes 48 23 = 2499364528492 :=
  by decide +kernel

theorem loss_bound (N : ℕ) : Bound envelope terminal plain boxes 20684909705004 N :=
  loss_of_chunks 1 envelope terminal plain boxes 20684909705004 N (by decide) (by decide)
    (LossSum.empty _ _ _ _
      |>.append 24 9732346388059 exactLoss0
      |>.append 24 8453198788453 exactLoss24
      |>.append 23 2499364528492 exactLoss48)

def receipt : KoalaSplitProof.Receipt envelope split unit :=
  ⟨terminal, plain, boxes, powers, plainPowers, tailPowers, 20684909705004,
    by decide,by decide,loss_bound,fun _ h h' => prices h h', tail⟩

end KoalaAt2428Gate15

#print axioms KoalaAt2428Gate15.loss_bound
#print axioms KoalaAt2428Gate15.receipt
