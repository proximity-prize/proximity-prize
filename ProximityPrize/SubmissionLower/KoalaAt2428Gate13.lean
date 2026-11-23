import ProximityPrize.SubmissionLower.KoalaGateSharedData
import ProximityPrize.SubmissionLower.KoalaGateChunkSums
import ProximityPrize.SubmissionLower.KoalaSplitGateWords

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000

set_option linter.defProp false

namespace KoalaAt2428Gate13
open KoalaGateSharedData
open FadicGate KoalaGateCheck
open KoalaWeightedRate (Envelope)
open KoalaFarBridge (rowCheck plainCheck)

def envelope : Envelope :=
  ⟨137,56,10,137,56,3562,4437,⟨2413401656553784320,11782525700909973120,11265360206149071360⟩,1054084729294884885120⟩
abbrev split:ℕ:=96
abbrev unit:ℕ:=490596702202131498240
abbrev terminal:ℕ:=72
abbrev gate:=KoalaSplitRow.rate envelope split unit

private def boxesTape : List (List Entry) := [
  unpack 1 0x1b5b57bd,unpack 2 0x48cdd5c1d6221ae,unpack 2 0x484c9981f125f18,unpack 3 0x4b8c574488d18a216f6d62,unpack 4 0x494f99c4b0b1bc488d17e231f9c5d,unpack 5 0x4b8c5c848ce5904b8c96a488d974252674bd,unpack 5 0x4b8c59c490e9a44bccd5c484dd76272d3eae,unpack 6 0x490f97c4bcc9b0488f1c64b8b97248cd9662933b203,
  unpack 6 0x4c0dd6e490e9f048cf1944b8c166488dd5e2b3a7bef,unpack 7 0x49515c049915e24b8bd8a488f1904c4bd5a480cda42ceab95e,unpack 8 0x4b8b16249915e24951daa4bcb9ac48cf9884b8a99e488e9482ef191be,unpack 8 0x4c4dd6a49109ee488f98a4c0bdc648cfd584bca990480d18e30a1c0b9,unpack 8 0x4c8f5ba490f1b6484e9944c4d5a6488e9924c0c540480d98432a89919,unpack 10 0x4c4d5a449529f84cce1e2491118e4c8d59a480d9cc488ed864bcb17a480d9843458d688,unpack 11 0x47cc15a4d50e1e488f97a4cce5e848cfdc848d05b04c8d96a480dd9c4c0b56c47cd97636096a86,unpack 11 0x4b0993a4b16e50478cd564d4f5e6484f5c848d05d64c8c570484f57e4c4b56047cc5bc3866055a,
  unpack 11 0x47cc54e4e54a3848d01984c8c59e48d2202488f5724c4b5a8480e1b84c4b55e480e5643a6cddba,unpack 12 0x480dd78488f9d44d909f84952df64ccc56e484f9e04ccc988485015e480eda04c09d7e47ccda83c1d1b29,unpack 12 0x474c55e49d421e4ccd58c49531ec4ccc9aa480f1bc488f9b04c8bd90480ed724c8b552474d5983dcdaf26,unpack 13 0x4a14236478c9504ad866c4bc994c49535e24d0cdc248501844c8bdaa480f1ba480f18c4c8a164478d9923fd430f2,unpack 13 0x484f9bc478c55e4ad8e7a4c09d3e48d262a4d4cd9e4850d90480f1d64d0b980480f9804c4a95c478d99441dafae4,unpack 14 0x4c5beb0474c96a484fde449956264d0d16e48905b44d0d5ae4890df2480f5804c8ad96480f9764c8a94e47cdd864437faba,unpack 14 0x4a97644474cd5e495423c48d19c44dcf1b6478dd8e4d4d5a048511f6480f99a4ccb17e480fd764c88d90474e5804592023f,unpack 14 0x49121ea46cc1904ad964a474c9a04e50dcc47cedc84d8d99247cedca481018e4ccb19a478ed8c4d0a93e478e57247ef0215,
  unpack 15 0x4cdc302474d97c470c1764a99e90474d55e4e4f6064851dd44d0b58c481058447cf1be4d0b18c47ced884ccb136474d1ac499f4df3,unpack 15 0x4b59684468c57c48511a049d6240470c9864e90dc84810a064d8d15e47cf58e48109c44cc9d8647cf1984c89d6e478ed684ba617e4,unpack 16 0x4d1cede4954a1446cc96e495520248931e647cfdc04e0dd9e48111f64d8b9964810db8478fd864d0a19c478f96c4d0995e474d9a24dac8b39,unpack 16 0x4d1dacc470f1ce46ccd624a98e64470edc048d31fc4d0b14e48111f64dcc17e48111ac478fdac4d4a18e478fd624d0a154474d5a04fb346b6,unpack 17 0x4ce51144c1ca80464b5b4468d15a4b1baa846cc98848d4e284d08d3648529d84dcc17e47905de47cfd784d0ada0478e5a24d09d54474e18c51639294,unpack 18 0x489059c4ce4d1a49d6a3e464d55e47901e84a18256468d17e48d521e4dcb56e478f9b64e4e58a474e1e8479098a4d8a976474e99a4d0a54a474e580536a6af4,unpack 19 0x4548d6a4b175ea4ca413e47d21be464cd7248d4a2a489422646cd57248d56124e4e1aa474e9ca4e0c972474f99e478f5c04d8a96c470f1924d8a53a46cd1c6551aa863,unpack 20 0x44c916045c9d384d1da584c22d5445cd962460d1644a18a9a4790dc8474fdb848539d04e4c9c847d1d984d8a1a847d1196470e5b24d8ad62474f5844d48d72470ed785721724f,
  unpack 21 0x7b012fa0dc8d6848109924cdd66249d6a204614c2c45ccd824b5ced4464d1684812e2247105b04ecdd9a47905de4dca96a47d119646cf1c24dcad60478f5764d0956a46cd5bc58d1afbe,unpack 21 0x4400f0644491524ad6e0c4c9da5847d19bc459502047501f64a19668460d58e48d623c468d57e4e8d5bc47909d44e0bd5647905ba47501ac4d89d68470e5b24dcad16468ddb45ad8881e,unpack 21 0x43c02f444899804cdd26c4c2312e45cd564458d18648956144895e2e460d9844916a24460c5b04f0e5a647915bc4e0a98247509bc47509964dca15c470e1b24d4995c470dda25cdeed03,unpack 21 0x34c8ac4746b648c1fe080b1cd7883c4298069600049d7eac47125f4464d97848962484750d8c4e8b57646cfdf24f0dd90468e9b847905944dca57446ced864dc954c46ce19a5ee5b6ef,unpack 21 0x2186aa8250af19262c3570144cdd68454d9744b1d6ca464f18a46d11c047d361047925ec4dc85684791da64ecc19c46d01be470f9a04e0a942470e99c4d8a14446ce59060ec8f4f,unpack 21 0x4126b1306cd2ec4709f1c01005257e46921c64a1723e45919ea47d41fa47111b24792a1a4e4a9504750dd64e4a58a47101ae46d01984e4a54046cf5944d8857c46ce98e629cccbe,unpack 21 0x84f79a384f8a808101d3dd047d3de448d326445d49304853e0845d3e5a47d3de24f0c18e46d01bc4e09d6047511a046cedce4e0a95c46cdda64dca52c470e98264f9cc95,unpack 21 0x408102040810153d8e8ed2a1400151544f13dea47112a646d11984e49d8e47509984e09d7e4710194464e5a04dc8d6c46ced7a6653d419,
  unpack 21 0x102040810204081179016639579d446d3d9e46d3d9c4e49e944710db446cf5b84e8ad42468e9924d89166470f16c68b0d3f0,unpack 21 0x8102040810204081481219a09959a84e13d9047d3da6460dea446cf9ac4e0a14e46ce9904dc9158464e1b46a0ae9e8,unpack 21 0x81020408102040811c93e084d13d9648cf9a636181b44653d7c4e8a67c46cf594460d9ce4e8a904464e5aa6c67e9bf,unpack 21 0x204081020408102040812553d903453dbc46d3d7a4e53d92468c29046cf19e4d88160468e1a86e1818ba,unpack 21 0x10204081020408102040812a93da4488f19c351897c4693d84464c6c44e49932464e9a0701ef11a,unpack 21 0x810204081020408102040812e13d863393d984693d964653d624e072c2464ed9471cf2e89,unpack 21 0x408102040810204081020408131d3d8030d3d924d53d6c4693d624608ed2742c2e60,unpack 21 0x204081020408102040810204081355315e34d498c4553d6e4753d5477368f1d,
  unpack 21 0x102040810204081020408102040812313d624693d424653d7e78e59cf8,unpack 21 0x102040810204081020408102040813dd3dda2d93d424593d867a3e74e8,unpack 21 0x8102040810204081020408102040813f93d8e488dd66a4556e71,unpack 21 0x4081020408102040810204081020408141d356aa6b2261c]
def boxes (r : ℕ) : List FadicGate.Entry :=
  if r < 20 then [] else boxesTape.getD (r-20) []

def plain : ℕ → ℕ × ℕ × ℕ
  | _ => (0,0,0)

private def powersTape : List String := [
  "","","","","","","","",
  "","","","","","","","",
  "","","","","!#","!#","!#&","!#&+",
  z4E,z4E,"!#%*/3","!#%)/4","!#%),5=","!#%)-5>?","!#%(-19>","!#%(.16?",
  "!#%(+17@KQ",z4R,z6A,"!#%(,/9>CWU",z5q,"!#%'+04:EJYW","!#$'+04;FE[Yi","!#$'+05;GF][a",
  z54,z55,"!#$&*.29=IJa_i","!#$&*.26>KIcaa~#$","!#$')/27>LK]cay","!#$&),27?GLVecp~#4","!#$&)-38@BMPgeh~#+","!#$&*-38A@NMige~##~#C",
  "!#$&)-09=AONcigx~#;~#C","!#$&)-059BPO]kip~#3~#G~#C",(zz77 ++ "G~#C"),"!#$&),14:CGRPomk~##~#C~#K~#G~#C",(zz76 ++ "#K~#G"),(zz69 ++ "#O~#K"),(zz67 ++ "#S~#O"),"!#$&(+/6<<EPUVusp}~#C~#W~#P",
  "!#$&(+/39<FKVToupl~#7~#[~#Q","!#$%(+/26=GEWUgvpk~#%~#M~#Q","!#$%(+/27=GGWV_vpkp~#;~#Q","!#$%(+027=HGYVTvpke~#)~#Q","!#$%'*-37>DGRVSmpkes~#?","!#$%'*-38??GLVScpkea~#,","!##%'*-48?=GEVSXpke_w","!#$%'*.18:=GEVSPpke_d",
  "!##%'+.057=GEVSPgke_X","!##%').037=GEOSP]ke_X","!##%'),037=BEISPRke_X","!##%'),037==ECSPMke_X",(zz82 ++ "Mae_X"),(zz82 ++ "MVe_X"),"!##%'(,-379<ECLPMMe_X"]
def powers (r : ℕ) : List ℕ :=
  if r=0 then [] else KoalaSplitGateWords.powers (powersTape.getD (r-1) "")

def plainPowers : ℕ → List ℕ
  | _ => []

def tailPowers:List ℕ:=KoalaSplitGateWords.powers "!##%'(,-376<ECEPMIe_XSMJseUF7)"

def priced (r:ℕ):Bool:=rowCheck gate r (boxes r) (powers r) (plain r) (plainPowers r)
private theorem priced_list : (List.range 71).all (fun i => priced (i+1)) = true := by decide +kernel

theorem prices {r : ℕ} (hr : 0 < r) (hR : r < terminal) : priced r = true :=
  price hr hR priced_list

theorem tail:plainCheck gate terminal (4012,1650,550) tailPowers=true:=by decide +kernel

private abbrev Chunk (i n v : ℕ) := lossChunk 24 envelope plain boxes i n = v
private theorem checkPart (i n v : ℕ) (ok : Chunk i n v := by decide +kernel) : Chunk i n v := ok
private def part0 := checkPart 0 6 0x2384dc4cc14
private def part1 := checkPart 6 6 0x2384dc4cc14
private def part2 := checkPart 12 6 0x2384dc4cc14
private def part3 := checkPart 18 6 0x23475e72eb3
private def part4 := checkPart 24 6 0x2263b22654c
private def part5 := checkPart 30 6 0x20bf01ef702
private def part6 := checkPart 36 6 0x1dfaa347ddd
private def part7 := checkPart 42 6 0x19b8e7188db
private def part8 := checkPart 48 6 0x133dbc27310
private def part9 := checkPart 54 6 0xb3f2db33cd
private def part10 := checkPart 60 6 0x561feda848
private def part11 := checkPart 66 5 0x282317145d

theorem loss_bound (N : ℕ) : Bound envelope terminal plain boxes 20825570761079 N :=
  loss_of_chunks 24 envelope terminal plain boxes 20825570761079 N (by decide) (by decide)
    (LossSum.empty _ _ _ _
      |>.append 6 0x2384dc4cc14 part0 |>.append 6 0x2384dc4cc14 part1 |>.append 6 0x2384dc4cc14 part2 |>.append 6 0x23475e72eb3 part3
      |>.append 6 0x2263b22654c part4 |>.append 6 0x20bf01ef702 part5 |>.append 6 0x1dfaa347ddd part6 |>.append 6 0x19b8e7188db part7
      |>.append 6 0x133dbc27310 part8 |>.append 6 0xb3f2db33cd part9 |>.append 6 0x561feda848 part10 |>.append 5 0x282317145d part11)

def receipt : KoalaSplitProof.Receipt envelope split unit :=
  ⟨terminal, plain, boxes, powers, plainPowers, tailPowers, 20825570761079,
    by decide,by decide,loss_bound,fun _ h h' => prices h h', tail⟩

end KoalaAt2428Gate13

#print axioms KoalaAt2428Gate13.loss_bound
#print axioms KoalaAt2428Gate13.receipt
