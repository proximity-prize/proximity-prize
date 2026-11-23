import ProximityPrize.SubmissionLower.KoalaAt2428Gate15
import ProximityPrize.SubmissionLower.KoalaGateSharedData
import ProximityPrize.SubmissionLower.KoalaGateChunkSums
import ProximityPrize.SubmissionLower.KoalaSplitGateWords

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000

set_option linter.defProp false

namespace KoalaAt2428Gate16
open KoalaGateSharedData
open FadicGate KoalaGateCheck
open KoalaWeightedRate (Envelope)
open KoalaFarBridge (rowCheck plainCheck)

def envelope : Envelope :=
  ⟨136,56,12,136,56,3536,4436,⟨2567926019269032960,13149498447048798720,6561057590419368960⟩,1115765063789518840320⟩
abbrev split:ℕ:=96
abbrev unit:ℕ:=495649102911829943040
abbrev terminal:ℕ:=72
abbrev gate:=KoalaSplitRow.rate envelope split unit

private def boxesTape : List (List Entry) := [
  unpack 1 0x17a37796,unpack 1 0x19aa3313,unpack 2 0x484bda21b5a707d,unpack 3 0x4b0c99048cd55c1d612bfa,unpack 4 0x490e9904b8c980484c1981f115af0,unpack 4 0x490e9864b8922048904de216e5ac6,unpack 5 0x4c0f996494f19c4b0b9bc488c97e231e89c1,unpack 6 0x4a129d04b8cdc848cdd904b8d56a488cd74252553ad,
  unpack 7 0x48ce58c49905b64b8d19c490e1a44b88a1a4891cb8272c0f2a,unpack 7 0x49505d4490f17c4bcd5b0488e5c64b8c17248cd1662932740b,unpack 7 0x49505d44c0ed6e490ddf048ce9944b8c966488d55e2b393df7,unpack 8 0x4c4f1c24950dc049909e24b8c98a48ce9944c0cd56480bda42ce96cf2,unpack 9 0x4a13a124b8bd6249509de498be984bd20c248ced884b8b19e488e1482ef036de,unpack 10 0x4b0a9304a94e444c4e96a490fdee484ed864c4cdca48cf1584bcb590480c58e30a05765,unpack 10 0x480bd404a9525e4c901ba490e9b6484dd944c4e1a6488dd924c0d540480c98432a72151,unpack 11 0x490aab04c53cba49521f84ccf1e2491058e4c8e59a480c9cc488e1864bcc17a480c9843457504c,
  unpack 11 0x47cb15a4d51e1e488f17a4ccf5e848cf1c848cf9b04c8e96a480cd9c4c0c56c480cd7a365e1a38,unpack 11 0x4b0a53a4b16a50478bd564d505e6484e9c848cf9d64c8d970484e57e4c4c56047cb5bc386470aa,unpack 12 0x499161447cb54e4e5623848cf5984c8d59e48d1202488e9724c4c5a8480d5b84c4c55e480d5643a6b3a96,unpack 12 0x480d178488edd44d91df849521f64ccd56e484ede04ccd988484f55e480dda04c0ad7e47cbda83c1b6991,unpack 13 0x4b992a8474b55e49d361e4cce98c49525ec4ccddaa480e1bc488edb04c8cd90480dd724c8c952478c59e3e22337d,unpack 13 0x4a13e36478b5504ad866c4bca54c49529e24d0e1c2484f1844c8d1aa480e1ba480e18c4c8b564478c9923fd270e6,unpack 14 0x4cdd6d8484edbc478b55e4ad8a7a4c0a93e48d1a2a4d4e59e484f990480e5d64d0cd80480e9804c4b95c478c99441d92c64,unpack 14 0x4c5beb0474b56a484f1e44994a264d0e56e488f9b44d0e5ae48901f2480e9804c8b996480ed764c8bd4e47cc98644361dc6,
  unpack 14 0x4a96e44474b95e495363c48d11c44dd09b6478c98e4d4e9a048501f6480ed9a4ccc17e480ed764c8a190474d180459016d7,unpack 15 0x4d5e2c449115ea46ca9904ad924a474b9a04e525cc47cd9c84d8f19247cd9ca480f18e4ccc99a478d98c4d0bd3e478d57247ed16ad,unpack 16 0x4b17e264cdcb02474c57c470ad764a99690474c15e4e50e064850dd44d0c98c480f58447ce1be4d0c58c47cdd884ccc536474c1ac499d5417,unpack 17 0x210d48e4d5dace4b59284468ad7c48505a049d5640470b5864e929c8480fa064d8e55e47ce58e480f9c44ccb18647ce1984c8b16e478d9684ba40f94,unpack 18 0x460914e48d48ec4d1d2de495421446cb16e49145fe48d21ea47cedc04e0f59e48101f64d8d196480fdb8478e9864d0b59c478e56c4d0b15e474c5a24daa7475,unpack 19 0x45c954446091484b16e284d22600470d9ce46cb9624a98a64470d5c048d25fc4d0c54e48101f64dcd97e48101ac478e9ac4d4b98e478e9624d0b554474c5a04fb12ff2,unpack 20 0x454953e458914e46499384d1d2b04be09b84649db4468bd5a4b1aea846cb98848d3e284d0a53648519d84dcd57e478f1de47ced784d0c5a0478d1a24d0b554474cd8c51616d5c,unpack 20 0x450914e45c915248905ac4cdd6a049da180464bd5e478ede84a17656468bd7e48d421e4dccd6e478e5b64e90590470c9e2478f58a4d8c176474d59a4ccb544478d98653683748,
  unpack 21 0x448993445095424548d604b176124c9d2b047d4d02464b57248d3e2a489322646cbd7248d46124e4fdaa474d5ca4e0e572474e19e478e1c04d8c56c46cd58c4dcc14046cbdc655186643,unpack 21 0x444954244c915645c9d324d1da964c1c6b045cfcac464b96849d7a96478fdc8474e5b848529d04e4e5c847d09984d8b9a847d0196470cdb24d8c962474dd844d4a972470d578571f21bb,unpack 22 0x68bd887b0993c0dc8d6048109a24cdd6a04a16e4845d009a45cb5824b5c6d4464b9684811e22470e9b04ecfd9a474f1d84e0c57047cfd9646cd9c24dcc960478e1764d0ad6a46cbdbc58cf50b6,unpack 22 0x42c4a28440993c448954c4a96a304c9da9447d19d44590890474edf64a18a68460b98e48d523c468bd7e4e8f1bc478f5d44e0d956478f1ba474edac4d8b568470d1b24dcc516468c5b45ad61aa2,unpack 22 0x42c7a3043c9156448993c4cdd2a84c1d2a845cc564458f4c24894a144894a2e460bd844915a24460adb04f105a6478fdbc4e0c982474f1bc474f5964dcb95c46cc9ac4d8b562470c9a25cdc7f87,unpack 22 0x3eccdde03475aa470fdac8c5cec20b1e17883c3a980693c0049d72ac4710df4464c1784894e48474f58c4e8d576470edf84ecf58a468d1b8478f1944dcc17446cd5864dcb14c46ccd9a5ee34973,unpack 23 0x28049ec42181d2c250b70f26308dd0144cad68454bd744b1ceca464d58a46cf5c047d26104790dec4dca16847909a64ece19c46ce9be470e1a04e0c542470d59c4d8b944468c9886093c087,unpack 23 0x28129ee0412431306cfaec4709f2d05004f95e46901c64a1be3e458a5ea47d29fa470f9b2479161a4e4c950474f9d64e0b984474f1b446ce9984e4c14046cdd944d8a17c46cd18e629a33e6,
  unpack 23 0xa14084f6fa384f93828501d3db047d3de448d327e45d39164854e0845c965a47d29e24f0e58e468e1b64e8c56c470f59a46cd5ce4e0c55c46cc9a64dcbd2c470d58264f733bd,unpack 23 0x50a142850a142850153d744852a9846950d04f109ea470a6a6471019e4e0b588474f5984e0b97e470e994464cda04dca56c46cd97a66512ccd,unpack 23 0x50a142850a142854813dee13d3e1e3553d504fd3dd446d399e46cf99c4e44a94470f9b446cddb84e4c53a468d1924dcb16e470dd6c68ae2ca4,unpack 23 0x142850a142850a1428513d3e063f9220646559284e1199047d05a646086a446ce1ac4e0c14e46ccd904dcad58464c9b46a0825b4,unpack 23 0xa142850a142850a142851c93e063893e06440fa064f580d2464f97c4e8527c46cdd94460bdce4e8c904464c9aa6c651717,unpack 23 0x2850a142850a142850a142852513d803493dbc46d3d7a4e4cd924687e9046cd99e4d89d60468c9a86e154612,unpack 23 0x142850a142850a142850a142851713e064353d2c4dd217c468f1844645ec44e4b932464cda0701c0ffe,unpack 23 0xa142850a142850a142850a142852e13d7a3393d984693196464f5624e00ec2464d59471cc3ef9,
  unpack 23 0x50a142850a142850a142850a1428531d3d7630d3d924d5056c468d5624605ad27429305c,unpack 23 0x50a142850a142850a142850a142854813dfe34d315e355498c454fd6e474e15477345b71,unpack 23 0x2850a142850a142850a142850a142854813e002313d624693d42464fd7e78e4b5b8,unpack 23 0x142850a142850a142850a142850a142854813dd42353d424593d867a3e74e8,unpack 23 0xa142850a142850a142850a142850a142854013d8a2a53d667c43b89d,unpack 23 0xa142850a142850a142850a142850a142854813e0440d356aa5594e6c]
def boxes (r : ℕ) : List FadicGate.Entry :=
  if r < 18 then [] else boxesTape.getD (r-18) []

def plain : ℕ → ℕ × ℕ × ℕ
  | _ => (0,0,0)

private def powersTape : List String := [
  "","","","","","","","",
  "","","","","","","","",
  "","","","!#","!#&","!#&*","!#&*","!#&+2",
  "!#&).9","!#&).49","!#%*/3;","!#%)/4<","!#%),5=E","!#%)-5>?M",z4i,"!#%(.16?QO",
  z4S,z4R,z6A,z4N,z5q,"!#%'+04:EJYWq","!#$'+04;FEZYi","!#$'+05;GF]Za~#$",
  z54,z55,z6i,"!#$&*.26>KIcaa~#$~#8",z6K,z5u,z5S,z2v,
  z5H,z2t,z4l,z3V,z4g,z4h,"!#$%(,.6<@EUT]sqo~#+~#K~#S~#O~#F","!#$&(+/6<<EPUVusq~#!~#C~#W~#S~#F~#7",
  (zz104 ++ "qn~#9~#[~#T~#F~#7"),"!#$%(+/26=GFWVhvqk~#(~#P~#U~#F~#7","!#$%(+/27=HFXV_wqkr~#?~#U~#F~#7","!#$%(+037>HGYVUwqkf~#,~#U~#F~#7","!#$%'*-37>DGSVSmqkfv~#B~#F~#7","!#$%'*-38??GLVScqkfc~#/~#F~#7","!##%'*.48?=GEVSYqkf`z~#F~#7","!#$%(*.18:=GEVSPqkf`g~#3~#7",
  "!##%'+.057=GEVSPgkf`Y}~#7","!##%').037=GEPSP^kf`Yj~#7","!##%'),037=BEISPSkf`YW~#$","!##%'),037==ECSPMkf`YSn",(zz82 ++ "Mbf`YSZ"),(zz82 ++ "MWf`YSN"),"!##%'(,-379<ECLPMMf`YSN"]

def powers (r : ℕ) : List ℕ :=
  if r=0 then [] else KoalaSplitGateWords.powers (powersTape.getD (r-1) "")

def plainPowers : ℕ → List ℕ
  | _ => []

def tailPowers : List ℕ := KoalaSplitGateWords.powers "!##%'(,-376<ECFPMJf`YSNKvgWH9*"

def priced (r:ℕ):Bool:=rowCheck gate r (boxes r) (powers r) (plain r) (plainPowers r)
private theorem priced_list : (List.range 71).all (fun i => priced (i+1)) = true := by decide +kernel

theorem prices {r : ℕ} (hr : 0 < r) (hR : r < terminal) : priced r = true :=
  price hr hR priced_list

theorem tail:plainCheck gate terminal (4012,1650,550) tailPowers=true:=by decide +kernel

private abbrev Chunk (i n v : ℕ) := lossChunk 12 envelope plain boxes i n = v
private theorem checkPart (i n v : ℕ) (ok : Chunk i n v := by decide +kernel) : Chunk i n v := ok
private def part0 := checkPart 0 6 0x2384dc4cc14
private def part1 := checkPart 6 6 0x2384dc4cc14
private def part2 := checkPart 12 6 0x2382111b865
private def part3 := checkPart 18 6 0x23329cad2c9
private def part4 := checkPart 24 6 0x22585a0368f
private def part5 := checkPart 30 6 0x20c609e0463
private def part6 := checkPart 36 6 0x1e28015d251
private def part7 := checkPart 42 6 0x19eb4686bb7
private def part8 := checkPart 48 6 0x13a9f0ec306
private def part9 := checkPart 54 6 0xb944593f10
private def part10 := checkPart 60 6 0x4f83d12057
private def part11 := checkPart 66 5 0x18ffbd3698

theorem loss_bound (N : ℕ) : Bound envelope terminal plain boxes 20802273080661 N :=
  loss_of_chunks 12 envelope terminal plain boxes 20802273080661 N (by decide) (by decide)
    (LossSum.empty _ _ _ _
      |>.append 6 0x2384dc4cc14 part0 |>.append 6 0x2384dc4cc14 part1 |>.append 6 0x2382111b865 part2 |>.append 6 0x23329cad2c9 part3
      |>.append 6 0x22585a0368f part4 |>.append 6 0x20c609e0463 part5 |>.append 6 0x1e28015d251 part6 |>.append 6 0x19eb4686bb7 part7
      |>.append 6 0x13a9f0ec306 part8 |>.append 6 0xb944593f10 part9 |>.append 6 0x4f83d12057 part10 |>.append 5 0x18ffbd3698 part11)

def receipt : KoalaSplitProof.Receipt envelope split unit :=
  ⟨terminal, plain, boxes, powers, plainPowers, tailPowers, 20802273080661,
    by decide,by decide,loss_bound,fun _ h h' => prices h h', tail⟩

end KoalaAt2428Gate16

#print axioms KoalaAt2428Gate16.loss_bound
#print axioms KoalaAt2428Gate16.receipt
