import ProximityPrize.SubmissionLower.KoalaAt2428Gate11
import ProximityPrize.SubmissionLower.KoalaGateSharedData
import ProximityPrize.SubmissionLower.KoalaGateChunkSums
import ProximityPrize.SubmissionLower.KoalaSplitGateWords

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000

set_option linter.defProp false

namespace KoalaAt2428Gate12
open KoalaGateSharedData
open FadicGate KoalaGateCheck
open KoalaWeightedRate (Envelope)
open KoalaFarBridge (rowCheck plainCheck)

def envelope : Envelope :=
  ⟨137,56,11,137,56,3562,4437,⟨2500980291016079040,12577243328709560160,8793628688288015520⟩,1094663502882673593120⟩
abbrev split:ℕ:=96
abbrev unit:ℕ:=493155744920571966720
abbrev terminal:ℕ:=73
abbrev gate:=KoalaSplitRow.rate envelope split unit

private def boxesTape : List (List Entry) := [
  unpack 1 0x17a3a2f2,unpack 1 0x19aa5e6f,unpack 2 0x484c1a21b5a9bd9,unpack 3 0x4b0c99048cd55c1d615756,unpack 4 0x490ed904b8c580484c5981f1194c0,unpack 4 0x490f1864b8c974488c98a216e9496,unpack 5 0x4c0f596494f19c4b0b5bc488cd7e231ec391,unpack 5 0x4b8c9c848ce1904b8cd6a488d17425258d7d,
  unpack 6 0x49505b24b8cd9c490e1a44bcd55c484d176272c48fa,unpack 7 0x49509d4490f17c4bcd1b0488e9c64b8bd7248cd5662932bc4f,unpack 7 0x49509d44c0e56e490e1f048ced944b8c566488d95e2b39863b,unpack 8 0x4c4edc249511c04990de24b8c58a48ced944c0c156480c5a42ce9b536,unpack 9 0x4a13e124b8b56249911e249515aa4bcc5ac48cf1884b8ad9e488e1482ef07f22,unpack 10 0x4b0a5304a952444c4e16a49101ee488f58a4c0c1c648cf9584bcad90480cd8e30a0ae1d,unpack 10 0x480c1404a9565e4c8f9ba490edb6484e5944c4d9a6488e1924c0cd40480d18432a77809,unpack 11 0x49105c64c4dda449525f84cce9e2491098e4c8dd9a480d1cc488e5864bcb97a480d1843457a704,
  unpack 11 0x47cb95a4d5161e488f17a4ccede848cf5c848d01b04c8e16a480d59c4c0b96c480d57a365e70f0,unpack 11 0x4b0a13a4b16a50478c1564d501e6484edc848cfdd64c8d170484ed7e4c4bd6047cbdbc3864d5d6,unpack 12 0x499161447cbd4e4e5563848cf9984c8cd9e48d1a02488f1724c4bda8480d9b84c4bd5e480dd643a6b9fc2,unpack 12 0x480d178488f5d44d911f849525f64ccd16e484f1e04ccd188480f95a484e5a44c0a57e47cc5a83c1bcebd,unpack 13 0x4b992a8474bd5e49d3a1e4cce18c49529ec4ccd5aa480e5bc484f1ac4ccc594480e5724c8c152478cd9e3e2298a9,unpack 13 0x4a13e36478c1504ad866c4bc9d4c4952de24d0d9c2484f9844c8c5aa480e9ba480e98c4c8a964478d1923fd2d612,unpack 14 0x4cddad8484edbc478c15e4ad8a7a4c0a13e48d222a4d4d99e4850190480e9d64d0c580480ed804c4b15c478d19441d99190,unpack 14 0x4c5beb0474bd6a484f5e44994e264d0dd6e488fdb44d0e1ae48501ee484f1844c8b196480f5764c8b14e47cd58644369166,
  unpack 14 0x4a97244474c15e4953a3c48d15c44dd01b6478d18e4d4e1a048505f6480f19a4ccb97e480f5764c89990474d98045908a77,unpack 15 0x4d1dec049119ea46cb1904ad964a474bda04e51dcc47ce1c84d8e59247ce1ca480f98e4ccbd9a478e18c4d0b53e478dd7247ed8a4d,unpack 16 0x4b182264cdc702474cd7c470b5764a99a90474c95e4e5060648511d44d0c18c480fd8447ce5be4d0bd8c47ce5884ccb936474c9ac499dc7b7,unpack 17 0x210e0744d5d6ce4b59284468b97c48509a049d5e40470bd864e91dc8480fe064d8dd5e47ce98e48101c44cca98647ce5984c8a96e478e1684ba48334,unpack 18 0x460915048cfdb64d221f8495461446cbd6e4954e0248925e647cf5c04e0e59e48109f64d8c59648105b8478f1864d0ad9c478ed6c4d0a55e474cda24daae815,unpack 19 0x45c954646091484b16e164d225f6470e5ce46cc1624a98a64470e1c048d29fc4d0bd4e48109f64dcc97e48109ac478f1ac4d4b18e478f1624d0a954474cda04fb1a392,unpack 20 0x454953e458915046499384d1d2964be0db6464a1b4468c95a4b1b2a846cc18848d42284d09d364851dd84dccd7e478f9de47cf5784d0b9a0478d9a24d0a954474d58c5161e0fc,unpack 20 0x450915045c915248905a44cdd68649da186464c55e478f9e84a17a56468c57e48d461e4dcc56e478edb64e8f990470d1e2478fd8a4d8b576474e19a4d0ad4a474d9805368aae8,
  unpack 21 0x448993445095424548d624b176004c9d29647d4d10464c17248d422a4893a2646cc97248d4a124e4f1aa474ddca4e0d972474e99e478e9c04d8b96c470e5924d8b13a46cc1c65518d9e3,unpack 21 0x444954244c915845c9d324d1da7c4c1c69645cfcc2464c56849d829647901c8474f1b848531d04e4d9c847d0d984d8b1a847d0596470d5b24d8bd62474e9844d49d72470dd78571fa3cf,unpack 22 0x68bd9c7b0993c0dc8d62481099a4cdd6864a16e3645d00b045cc1824b5cad4464c5684812222470f5b04ecf19a478f9de4dcb56a4790190470e9c84dcb960478e9764d0a56a46cc5bc58cfd2ca,unpack 22 0x42c4644440993c448954e4a96a204c9da7a47d19c845508a4478f5fa4a19268460c58e489563646cc9844e8e5bc478fdd44e0c956478fdba474f1ac4d8ad68470d9b24dcb916468cdb45ad69cb6,unpack 22 0x42c7a2c43c9178448993e4cdd28e4c1d28e45cc560458f8da4894e14489522e460c9844915e24460b9b04f0f5a647909bc4e0b982474fdbc474fd964dcad5c470d9b24d4a55c470cda25cdd019b,unpack 22 0x3ecd6080346dca470fda28c5ceac0b1d57883c4298069440049d76ac47115f4464c9784895a48475018c4e8c576470f5f84ece98a468d9b8478f9944dcb57446cdd864dca54c46cd59a5ee3cb87,unpack 22 0x49ed92184ca824eaf17264e1590144c661e45504be4b1d2ca464e18a46d01c047d2e1047915ec4dc956847911a64ecd19c46cf5be470eda04e0b542470e19c4d8a94446cd99060ea9573,unpack 22 0x129ef5412471306cf6ec4709f1c01004ed7e4690dc64a1be3e458b5ea47d35fa47105b24791a1a4e4bd5047501d64e4b18a470f9ae46cf1984e4b54046ce5944d8957c46cd98e629ac46e,
  unpack 22 0x4084f79a384f8a808101d39d047d41e448d326445d49304853e0845cbe5a47929dc4f4d99446cf5bc4e4b166471019a46cddce4e0b95c46cd1a64dcb12c470dd8264f7c445,unpack 22 0x20408102040810153d8e5812a1436d51544f121ea470aea64710d9e4e0a988474f9984e0ad7e470f194464d9a04dc996c46ce17a6651bd55,unpack 22 0x81020408102040810113d664fd3dd446d3d9e46d219c4e43a9446cfdac470edc04e8bd42468dd924d89d66470e56c68aebd2c,unpack 22 0x4081020408102040810b52208465593a4e12d9047d0da646092a446cedac4e0b14e46cd9904dca158464cdb46a08b63c,unpack 22 0x4081020408102040811c93e08495359048901ac3a181b4465257c4e8427c46ce594460c9ce4e8b904464d5aa6c65b613,unpack 22 0x10204081020408102040812193d903813dbc46d3d7a4e4e992468869046ce19e4d89560468d1a86e15e50e,unpack 22 0x810204081020408102040812713da43353d9c4dd3d7c468fd8446466c44e4a932464d9a0701caefa,unpack 22 0x40810204081020408102040812a1357e37945a04693d9646519624e002c2464dd9471ccddf5,
  unpack 22 0x2040810204081020408102040812dd3d8034d3d924d5216c464d95a4646ada7429ddcc,unpack 22 0x10204081020408102040810204081311315e391498c455216e474ed54773508e1,unpack 22 0x1020408102040810204081020408137d3e083353d624693d424652d7e78e56328,unpack 22 0x8102040810204081020408102040813a53dda3113d424593d867a3e74e8,unpack 22 0x408102040810204081020408102040813b53d8e2f13d667c43b89d,unpack 22 0x20408102040810204081020408102040813d1356aa04c2598,unpack 22 0x20408102040810204081020408102040814493e08aa669477]
def boxes (r : ℕ) : List FadicGate.Entry :=
  if r < 18 then [] else boxesTape.getD (r-18) []

def plain : ℕ → ℕ × ℕ × ℕ
  | _ => (0,0,0)

private def powersTape : List String := [
  "","","","","","","","",
  "","","","","","","","",
  "","","","!#","!#&","!#&*","!#&*","!#&+2",
  z4E,"!#&).5","!#%*/3;","!#%)/4<","!#%),5=E","!#%)-5>?M",z4i,"!#%(.16?QO",
  z4S,z4R,z6A,z4N,z5q,"!#%'+04:EJYWq","!#$'+04;FE[Yi","!#$'+05;GF]Za~#$",
  z54,z55,z6i,"!#$&*.26>KIcaa~#$~#8",z6K,z5u,z5S,z2v,
  z5H,z2t,z4l,(zz72 ++ "#<"),z4g,z4h,(zz67 ++ "#S~#O~#E"),(zz68 ++ "#W~#S~#E"),
  (zz104 ++ "qn~#9~#[~#T~#E"),"!#$%(+/26=GFWUhwqk~#'~#P~#T~#E","!#$%(+/27=GGXV`wqkr~#>~#T~#E","!#$%(+037>HGZVUwqkf~#+~#T~#E","!#$%'*-37>DGSVSmqkfu~#B~#E","!#$%'*-38??GLVSdqkfb~#/~#E","!##%'*-48?=GEVSYqkf`y~#E","!#$%(*.18;=GEVSPqkf`f~#3",
  "!##%'+.057=GEVSPgkf`Y}","!##%').037=GEPSP^kf`Yj","!##%'),037=BEISPSkf`YV","!##%'),037==ECSPMkf`YS",(zz82 ++ "Mbf`YS"),(zz82 ++ "MWf`YS"),"!##%'(,-379<ECLPMMf`YS","!##%'(,-376<ECFPMJf`YS"]

def powers (r : ℕ) : List ℕ :=
  if r=0 then [] else KoalaSplitGateWords.powers (powersTape.getD (r-1) "")

def plainPowers : ℕ → List ℕ
  | _ => []

def tailPowers : List ℕ := KoalaSplitGateWords.powers "!##$&(*-046<@CAPMJ[`YSMHbfVG8)"

def priced (r:ℕ):Bool:=rowCheck gate r (boxes r) (powers r) (plain r) (plainPowers r)
private theorem priced_list : (List.range 72).all (fun i => priced (i+1)) = true := by decide +kernel

theorem prices {r : ℕ} (hr : 0 < r) (hR : r < terminal) : priced r = true :=
  price hr hR priced_list

theorem tail:plainCheck gate terminal (4012,1650,550) tailPowers=true:=by decide +kernel

private abbrev Chunk (i n v : ℕ) := lossChunk 12 envelope plain boxes i n = v
private theorem checkPart (i n v : ℕ) (ok : Chunk i n v := by decide +kernel) : Chunk i n v := ok
private def part0 := checkPart 0 6 0x2384dc4cc14
private def part1 := checkPart 6 6 0x2384dc4cc14
private def part2 := checkPart 12 6 0x2382075dfda
private def part3 := checkPart 18 6 0x233180245a1
private def part4 := checkPart 24 6 0x22593902868
private def part5 := checkPart 30 6 0x20bb01c21b6
private def part6 := checkPart 36 6 0x1e1334e4396
private def part7 := checkPart 42 6 0x19c7d405550
private def part8 := checkPart 48 6 0x1373d063820
private def part9 := checkPart 54 6 0xb5f65f6fbe
private def part10 := checkPart 60 6 0x4dfa9476dd
private def part11 := checkPart 66 6 0x1d04d3d6b4

theorem loss_bound (N : ℕ) : Bound envelope terminal plain boxes 20766083683862 N :=
  loss_of_chunks 12 envelope terminal plain boxes 20766083683862 N (by decide) (by decide)
    (LossSum.empty _ _ _ _
      |>.append 6 0x2384dc4cc14 part0 |>.append 6 0x2384dc4cc14 part1 |>.append 6 0x2382075dfda part2 |>.append 6 0x233180245a1 part3
      |>.append 6 0x22593902868 part4 |>.append 6 0x20bb01c21b6 part5 |>.append 6 0x1e1334e4396 part6 |>.append 6 0x19c7d405550 part7
      |>.append 6 0x1373d063820 part8 |>.append 6 0xb5f65f6fbe part9 |>.append 6 0x4dfa9476dd part10 |>.append 6 0x1d04d3d6b4 part11)

def receipt : KoalaSplitProof.Receipt envelope split unit :=
  ⟨terminal, plain, boxes, powers, plainPowers, tailPowers, 20766083683862,
    by decide,by decide,loss_bound,fun _ h h' => prices h h', tail⟩

end KoalaAt2428Gate12

#print axioms KoalaAt2428Gate12.loss_bound
#print axioms KoalaAt2428Gate12.receipt
