import ProximityPrize.SubmissionLower.KoalaAt2428Gate9
import ProximityPrize.SubmissionLower.KoalaGateSharedData
import ProximityPrize.SubmissionLower.KoalaGateChunkSums
import ProximityPrize.SubmissionLower.KoalaSplitGateWords

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000

set_option linter.defProp false

namespace KoalaAt2428Gate10
open KoalaGateSharedData
open FadicGate KoalaGateCheck
open KoalaWeightedRate (Envelope)
open KoalaFarBridge (rowCheck plainCheck)

def envelope : Envelope :=
  ⟨137,56,13,137,56,3562,4437,⟨2617010426141989440,13888288279743148320,4744463700061340640⟩,1148926261182433512480⟩
abbrev split:ℕ:=96
abbrev unit:ℕ:=497435045946087912960
abbrev terminal:ℕ:=73
abbrev gate:=KoalaSplitRow.rate envelope split unit

private def boxesTape : List (List Entry) := [
  unpack 1 0xe2e906e,unpack 1 0xf886c96,unpack 2 0x490d56e11e56c70,unpack 3 0x4b8ed5448cbdb213ebc2e2,unpack 3 0x4a8bdbe494dd5415f27e5b,unpack 4 0x498edde4b4d96848cc99217a2ad52,unpack 5 0x4b901d6494e97e4b4cd8848cc99219a95a5d,unpack 5 0x4a519a84b4dda8498e190484b5aa1b598954,
  unpack 6 0x4a115b64b4d98e494e1dc4b0dd6248cbd8c1d60365e,unpack 7 0x4a535a8498dde44b4f196490d1c24b4cd76488bda21f106555,unpack 7 0x4a935c8490ce164bcf99e490e58e4b8d56e488d15c216d9ee2,unpack 8 0x4a0a54e4a91a3649509744c0e9c4494e9a44acb9b248cc58a231d7741,unpack 8 0x4bcf978494e1de4a125d44b8d1c448cd5964b8d964488c57c252432ba,unpack 9 0x49d09fe4cd3dda490d1c4494fdb84b8d594490d9ac4bcdd56484c57e272adfc4,unpack 9 0x48cc5544cd29fe49915aa490d5b84bced74488ca044b8dd3448cb5a2293144a5,unpack 9 0x480a1744d945e0494fddc4c0f166490edc048ccdd24b4c95c48cd16a2b38001f,
  unpack 10 0x4cd31e8494f5b84c4f9ba49505c84991da84b8b5c448cf95a4c0b98e480b5ae2ce820a7,unpack 10 0x4b8f13c4a1224e4b8d526498f21e4950db04bccda648ce5904b4b59248cd9542eeedc20,unpack 11 0x4c1aaba4b0ad2a4a94a4a4c4f16248cf1f248ce9984c0d1ba48ce9624bcbd86480bd98309efca8,unpack 12 0x4b556964d94a2e480b14a4a966244c8f1f2490e1bc484d59e4c5015e488bdda4c0f0f8480a9cc32a5b821,unpack 13 0x47c8d6c4d5e6b248cf5ca4c8eda04951a004ccf9d8490fd964c8ed8e480c1d8488f5444bca9bc480dd4234563db0,unpack 13 0x49905cc4c9cae247ca9624d52614488e5844ccfdde48ce9d048cf1ba4c8f15e480c5a84bcc560484c986365c9423,unpack 14 0x478954c4b96e604b16e764b0a9344ad6252478b1624d915de484ddd248cf1de4c8e166484dd884c4cd5447cadc63862ea95,unpack 15 0x47ca1364788d704d1dec24990e1c47cad584e581ec48cd5e04c4f1524911206488c5c44c4cd9e480c9c04c4cd56480cd6c3a69a60e,
  unpack 15 0x474916a498fdd84cdd6da480c584488e5dc4d925ec4951a004ccf922484e5e04ccc9c6480e566484d5b04c0d12847c99fc3c19c697,unpack 16 0x478b8f4478799c4b56e4e4b98eac474a96a49d32264ccf1804951df44cce5a0480d5c648905644c8d190480b9c84c8ecfc478bd9e3e20f585,unpack 16 0x474a12e47895544c9bf0c4a53a40478c9124ad62bc4bcad4449521ea4d0e9b6484e98e4c8d99e480d5c6480d9984c8d90a478a1ec3fd0b107,unpack 17 0x4709144474a52249505ca4cdd6d8484cdfe478ad684ad82804bcc8e8490fa824d4ed90484f19c480d9e04d0d974480dd8c4c4c150478bd9e41d75e11,unpack 18 0x4ad3dfa470953a47089724b16a4a4c9d68047495ac484e5ee49961da4d0cdba48911684d0d1f6488f5fc47cfd284cca5f048105224c8a1a047cc19244344f75,unpack 18 0x47cc18846c953a470915c4d5d6d44a96a4a474ad6c4952e4448d05ce4dd315e478a1e64d51148484f9f647cbdf64d0f122480c1d64c8ad82474e92e458ebbf7,unpack 19 0x4c16a6046c953a6889d24274f5ee4d1dec048d09f0470a1a04ad8a54474adac4e12dba480d5d84d8f98447cf17e480c5f24ccf136474a9ea4d4ece0478a9d447eb2b76,unpack 19 0x490fdbc464914846c953a4b17a284cdc706474b988470bd3a4a972e2474b56c4e51df648501e04ccd178484ed9647cd5ca4d0d17e478cd904d0d12e474b5b8499b5a6d,
  unpack 20 0x4e1ae80460953e6bc9538210895e4d1d2c84b9928e468a18a485156249d3294470cd324e9121a480ee124d8f15047cd99a480edd04ccbd7847cd5a44c8b962474c9704b4bc315,unpack 20 0x4a12e184649930460914648cfdc04d1d2da495362046cbd3c495264e48915f047ce1ce4e1018c48119a44d8b9e647cedc047d092e4d099f847901104d095ba470b1a84d521982,unpack 21 0x4e5aab2470c56e45c953c46091444b16e304d1daca46cc9da470ad744a99e22470ae1a48d1a084d0d13e480f6044dce56c47cf1b6478ddb84d8ed26478b9ce4d0c144474e1444fafa9b6,unpack 21 0x4bd6e46454953a458914846499324d1d2c24bdbe7e4648dc4468ad6a4b1aab246ca99648d32344d0b1264850de64d9011247cca4647ce1864d0cd92478c5ae4d0e4e64749df8515f485a,unpack 22 0x4e9aea8480fdb0450914845c914a48501ac4d1dab649d5244460a96c47ce5fa4a16e5e468ad9048d5dc04dcb5c8478d9c24e91180470bdf0478e9984d8cd66474c9a84d0e8da474a1ee536603d3,unpack 22 0x4d9a68e448992e450953e4548d5a4b1761c4c5cebe48101ca464a58448d3234489263446cd52248d167e4e50998474c9d84dced5e478d9b247901584d49dcc470f92c4dca5a246cadd45516245b,unpack 23 0x4e9aea84913202444953c44c915045c9d2c4d1daa84c1c6c045ca972460a5764a176a4474e9d2478ddcc4851dde4e4f5b447cf9a84d8c99647cf1a4470c1c24d4cd4c478d9984d4b56046cc18256c68cfe,unpack 23 0x8c1b690068bd7e7b099360dc8d5a48109a44cdd6b44a16e5045cad6445ca1944b5c2dc464a97a47d0a2c474e1c44ed3128474be464e0d55e47d193a4689a384dcfce447cb5f44d0b95a46cdd5458cd9f1e,
  unpack 24 0x8d58b080b991de428913e4449d3a44895444a96a3c4c9daa447d19d8454bd32478d2324a18274460a9a048d464a468d91a4e8d61e478e9e24e108e6478c226474ddbc4d8c558470c1c04d8cd0046cbdc85ad3bbd6,unpack 24 0x4fda2080212de4428856e440955244495344d1d6bc4c1d2ba45cc5624589d944893a244893e3e460ad964914e30460c94a4ece60447cf5d24e0f90e474c22c474e5a64dcc94a470c1c04d4e4e0470921c5cda1248,unpack 24 0x813ec8a08034b8e047501b08c18b880b1e19283c3e7e0691c2c49d7e8046cfdee46899d84894256474e99c4e8e56247109944ecd9ec468c1c8478e5a24dccd6446cf5164d889b246cbdaa5e8a7aea,unpack 25 0x4081004e5e44308d524a5722c4c5daa04813e044489966458a9864b1da9e460c984470ce2247d162047901fa4d8a95047d01bc4ecf18846cd9ce470d5b04e0d13046cc1a44dccd3a46cc1a060e7893b,unpack 25 0x20408129af5412231306d0901470b50701004b19a468fdaa4a1be3e45891ea47d21fa470f1b2478de984e500d2474c24e4e4d176471094a468a6184e904c046ca2184d8b16846cc1a06297a9c3,unpack 25 0x810204084b79a38538a808101cfdee47d59c648d5664458b57a48989be45c6a5a47d21e24f0ed8e46cb2384e4d152470e5aa46cc5de4e100d446c8e2c4dccd1a470c59064f49b26,unpack 25 0x408102040810204081015198e4854e78468e8f04f101ea470a2a6470f59e4e0c188474be124e0c96a470d9a6464bdb04dce0e446c9e00664e85c4,unpack 25 0x4081020408102040810913e088713e080112d664fcf9d446d159e46cba224e48a0e470c23046d013c4e8a9bc468f5184d885de470cd7c68ab7728,
  unpack 25 0x10204081020408102040811793e083bd21f6465254c4e0d99047cd614460a63646cd9ac4e099ca46cc1a04d8b53e468bdce6a0561c6,unpack 25 0x810204081020408102040811c93e083893e024412d3a4f09e20468ed984e891f446ca61245ca5d84ece0f6464b9bc6c625329,unpack 25 0x2040810204081020408102040810f93e044a1154846cf97a4e48e06468a21c46ccd9e4d4a15846c923e6e1273b1,unpack 25 0x1020408102040810204081020408116d360043929404dcb97c468b60c4648a3c4e4c132460862a6fc2dc53,unpack 25 0x8102040810204081020408102040811813dfa4990924468d596464ae004e05a24460c18c7173c6e9,unpack 25 0x408102040810204081020408102040811a93dfc480f9164d4c16c46899ea460864a74270b24,unpack 25 0x4081020408102040810204081020408133d3e082fd31ea4e8e100454cd6e474a1f077314f47,unpack 25 0x20408102040810204081020408102040813193e083992d62468d942460c976788c20c0,
  unpack 25 0x1020408102040810204081020408102040812cd3e083e92114458d1867a3c8980,unpack 25 0x81020408102040810204081020408102040812713e0843518ec7c433689,unpack 25 0x810204081020408102040810204081020408141d3e0829d36087df2a9df,unpack 25 0x4081020408102040810204081020408102040813cd36009ff5eff7]
def boxes (r : ℕ) : List FadicGate.Entry :=
  if r < 13 then [] else boxesTape.getD (r-13) []

def plain : ℕ → ℕ × ℕ × ℕ
  | _ => (0,0,0)

private def powersTape : List String := [
  "","","","","","","","",
  "","","","","","","!$","!$(",
  "!$'","!$'.","!$'+4","!#',5","!#&,09","!#&*06A","!#&*17C","!#&+28EC",
  "!#&).9?E","!#&).59GQ","!#%*/3:II",z5A,"!#%),5=EKX",z4j,"!#%(-19>OMi","!#%(.16?QOau",
  "!#%(+17@KQXyu","!#%',28AESQqy","!#%(,38CAUSi}y",z6l,z6k,z6U,z6F,z5s,
  "!#$'*-5<BGV]Zy~#0~#,~#(v",z5i,"!#$&*.29=IJa_i~#,~#4~#0~#,v",z53,"!#$')/27>LK]cax~#<~#8~#4~#0v",z4v,(zz95 ++ "~#8~#1v"),z4b,
  (zz94 ++ "@~#<~#1v"),z4Z,(zz77 ++ "G~#C~#@~#1v"),z4P,(zz76 ++ "#K~#G~#C~#1v"),z4L,z4K,(zz68 ++ "#W~#S~#I~#9~#*w"),
  (zz104 ++ "rp~#;~#[~#W~#I~#9~#*w"),"!#$%(+/26=GFWViwrl~#*~#S~#X~#I~#9~#*w","!#$%(+/27=HGXW`xrlt~#A~#X~#I~#9~#*w","!#$%(+037>HHZWVxrlf~#.~#X~#I~#9~#*w","!#$%'*-38>DHSWTnrlfx~#E~#I~#9~#*w","!#$%'*-38??HLWTdrlfd~#2~#I~#9~#*w","!##%'*.48?=HFWTZrlfa{~#I~#9~#*w","!#$%(*.18;=HFWTPrlfah~#5~#9~#*w",
  "!##%'+.057=HFWTPhlfaZ~#!~#9~#*w","!##%').037=HFPTP^lfaZl~#9~#*w","!##%'),037=BFITPTlfaZX~#&~#*w","!##%'),037==FDTPMlfaZTp~#*w","!##%'),037=<FDTPMbfaZT[~#*w","!##%'),037=<FDTPMXfaZTNsw","!##%'(,-379<FDMPMNfaZTN`w","!##%'(,-376<FDFPMJfaZTNLw"]

def powers (r : ℕ) : List ℕ :=
  if r=0 then [] else KoalaSplitGateWords.powers (powersTape.getD (r-1) "")

def plainPowers : ℕ → List ℕ
  | _ => []

def tailPowers : List ℕ := KoalaSplitGateWords.powers "!##$&(*-046<@DBPMJ]aZTNHdhWH8)"

def priced (r:ℕ):Bool:=rowCheck gate r (boxes r) (powers r) (plain r) (plainPowers r)
private theorem priced_list : (List.range 72).all (fun i => priced (i+1)) = true := by decide +kernel

theorem prices {r : ℕ} (hr : 0 < r) (hR : r < terminal) : priced r = true :=
  price hr hR priced_list

theorem tail:plainCheck gate terminal (4012,1650,550) tailPowers=true:=by decide +kernel

private theorem exactLoss0 : lossChunk 1 envelope plain boxes 0 24 = 9726854061656 :=
  by decide +kernel

private theorem exactLoss24 : lossChunk 1 envelope plain boxes 24 24 = 8469964969726 :=
  by decide +kernel

private theorem exactLoss48 : lossChunk 1 envelope plain boxes 48 24 = 2579147208706 :=
  by decide +kernel

theorem loss_bound (N : ℕ) : Bound envelope terminal plain boxes 20775966240088 N :=
  loss_of_chunks 1 envelope terminal plain boxes 20775966240088 N (by decide) (by decide)
    (LossSum.empty _ _ _ _
      |>.append 24 9726854061656 exactLoss0
      |>.append 24 8469964969726 exactLoss24
      |>.append 24 2579147208706 exactLoss48)

def receipt : KoalaSplitProof.Receipt envelope split unit :=
  ⟨terminal, plain, boxes, powers, plainPowers, tailPowers, 20775966240088,
    by decide,by decide,loss_bound,fun _ h h' => prices h h', tail⟩

end KoalaAt2428Gate10

#print axioms KoalaAt2428Gate10.loss_bound
#print axioms KoalaAt2428Gate10.receipt
