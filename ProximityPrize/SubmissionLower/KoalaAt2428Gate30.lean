import ProximityPrize.SubmissionLower.KoalaAt2428Gate29
import ProximityPrize.SubmissionLower.KoalaGateSharedData
import ProximityPrize.SubmissionLower.KoalaGateChunkSums
import ProximityPrize.SubmissionLower.KoalaSplitGateWords

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000

set_option linter.defProp false

namespace KoalaAt2428Gate30
open KoalaGateSharedData
open FadicGate KoalaGateCheck
open KoalaWeightedRate (Envelope)
open KoalaFarBridge (rowCheck plainCheck)

def envelope : Envelope :=
  ⟨132,55,12,135,55,3432,4435,⟨9693562945,53219475037,11267167823⟩,4200851234672⟩
abbrev split:ℕ:=48
abbrev unit:ℕ:=1919968400640
abbrev terminal:ℕ:=70
abbrev gate:=KoalaSplitRow.rate envelope split unit

private def boxesTape : List (List Entry) := [
  b05k,b04t,b040,b037,b033,b022,b010,b00w,
  bzz.take 6++unpack 1 0x19fcbd40,bzv,by2.take 7++unpack 1 0x1affb5b0,bxc.take 7++unpack 2 0x48c9d741c033ef3,byj,bvt.take 7++unpack 3 0x4a0d1804c13218236ff298,bvs.take 8++unpack 2 0x49cb54820664cd8,buc.take 8++unpack 3 0x4c95218490a18a21c01a86,
  bu9.take 8++unpack 3 0x4a0f1cc4b0f5ae25ccc72a,btj,bt0.take 9++unpack 3 0x264b92f6926795e57,bs6.take 9++unpack 3 0x4c121c6498a570287fa644,br2.take 9++unpack 4 0x4f1d2c849cbd904a4e9b22b8985ca,brn,boq.take 10++unpack 5 0x24a4ca8274e1722609915652b89b133,bnc.take 10++unpack 6 0x49499504b0fdb84f1cae04a0e1c64a0a5502e3c64e8,
  bn5.take 10++unpack 7 0x494995049091544d15e524e1bab84a0a5504a4e9d631464480,boc,bml,bkr.take 12++unpack 6 0x4909540494a1524d5665c4f1ced2490ad68319cc2b1,bk2.take 11++unpack 8 0x4909540494a15249495404e9ceda4d97e7c4a4b1564a0e5b2375972d7,bj9.take 12++unpack 7 0x494a15249495404b509b64e5c30c4cd31ea4949d623655ccc3,bjp,bfm.take 12++unpack 8 0x4949540494a53249095564f5c6e04e19aa6498b54e48c9d74395fd7b2,
  bgx,bh9,bdg,bdt,b4s.take 13++unpack 10 0x4e1724643891c648069c449ca1304d16e624f9e2984ad05f64989d904a4edc043295fe5,b4t.take 13++unpack 10 0x2b450e9bc4885df048899664f9de964fe0a4049495e249085c84c531f847e2784d,b83,b8h.take 14++unpack 9 0xac7a1e5cda270bd042a0bd280f43d15c84907de8478c3385,
  b50.take 14++unpack 9 0x2b1e939fb809f2ec903c7ab43d1dc44c9c2099,b2c,b2k,b2r,b2w,b34,b3a,b3l,
  b3p,b41,b3v,b4a,b4e]
def boxes (r : ℕ) : List FadicGate.Entry :=
  if r < 17 then [] else boxesTape.getD (r-17) []

def plain : ℕ → ℕ × ℕ × ℕ
  | _ => (0,0,0)

private def powersTape : List String := [
  "","","","","","","","",
  "","","","","","","","",
  "","!#","!#&","!#&+","!#&+",z3r,z2Q,z4F,
  "!#%(-8>",z41,z5l,z3q,"!#%(+3<DJ",z49,z6L,"!#$'-05>OM_",
  z68,z4M,z3y,z3x,"!#$&).48BOUVw","!#$&*.28CIWUo~#&",z3o,z6D,
  "!#$&),4;AETZYv~#.~#*~#&",z61,z5e,z3t,"!#$&(-05=JIZa_v~#9~#5~#1~#.","!#$%(+16=EJTcan~#1~#9~#5~#1",z3k,"!#$%),27?>LKgec~!~~#A~#=~#9~#5",
  "!!#%(,/7;?MLageu~#9~#A~#=~#9~#/","!!#%(,.47@NMYigm~#0~#E~#A~#=~#9","!!#%(*/28@INSjig~#(~#H~#E~#A~#=~#/","!!#%(*/38ADONlji}~#@~#H~#E~#A~#;","!!#%'+/39BAPOflju~#8~#L~#H~#E~#@~#/","!!#%'+039BBRP`nlm~#0~#P~#L~#H~#@~#2","!!#%'+-4:>BSRYpnl~#(~#H~#P~#L~#@~#2","!!#%')-4::CNSSrplw~#?~#T~#N~#@~#2",
  "!!#%'*-17:DITRlrlg~#2~#W~#N~#@~#2","!!#%'*.04;EDURcrlg|~#I~#N~#@~#2~#%","!!#%'*.15;EDURYrlgj~#6~#N~#@~#2~#%","!!#%'*.15<FDURPrlgb~#$~#N~#@~#2~#%","!!#$&),16<ADORPhlgbo~#;~#@~#2~#%","!!#$&),16<<DHRP^lgb]~#)~#@~#2~#%","!!#$&),26<;DBRPTlgb]s~#@~#2~#%","!!#$&),/68;DBRPMlgb]a~#.~#2~#%",
  "!!#$&),.25;DBRPMcgb]Vx~#2~#%","!!#$&(,.15;DBLPMXgb]Vf~#2~#%","!!#$&(*.15;?BEPMNgb]VR}~#%","!!#$&(*.15;:BAPMJgb]VQk~#%","!!#$&(*.15;9BAPMJ]b]VQW~#%"]

def powers (r : ℕ) : List ℕ :=
  if r=0 then [] else KoalaSplitGateWords.powers (powersTape.getD (r-1) "")

def plainPowers : ℕ → List ℕ
  | _ => []

def tailPowers : List ℕ := KoalaSplitGateWords.powers "!!#$&(*.15;:BAPMJSb]WRMqviZM?2$"

def priced (r:ℕ):Bool:=rowCheck gate r (boxes r) (powers r) (plain r) (plainPowers r)
private theorem priced_list : (List.range 69).all (fun i => priced (i+1)) = true := by decide +kernel

theorem prices {r : ℕ} (hr : 0 < r) (hR : r < terminal) : priced r = true :=
  price hr hR priced_list

theorem tail:plainCheck gate terminal (4012,1650,550) tailPowers=true:=by decide +kernel

private abbrev Chunk (i n v : ℕ) := lossChunk 12 envelope plain boxes i n = v
private theorem checkPart (i n v : ℕ) (ok : Chunk i n v := by decide +kernel) : Chunk i n v := ok
private def part0 := checkPart 0 6 0x2384dc4cc14
private def part1 := checkPart 6 6 0x2384dc4cc14
private def part2 := checkPart 12 6 0x237de8a4bdf
private def part3 := checkPart 18 6 0x23208029ffe
private def part4 := checkPart 24 6 0x224f195b4d9
private def part5 := checkPart 30 6 0x20c4ecf6d63
private def part6 := checkPart 36 6 0x1e1548cb9db
private def part7 := checkPart 42 6 0x19d80883dd8
private def part8 := checkPart 48 6 0x1397af167d0
private def part9 := checkPart 54 6 0xbd5d61b432
private def part10 := checkPart 60 6 0x5ae1153f0f
private def part11 := checkPart 66 3 0x1573d9ca8a

theorem loss_bound (N : ℕ) : Bound envelope terminal plain boxes 20829598565263 N :=
  loss_of_chunks 12 envelope terminal plain boxes 20829598565263 N (by decide) (by decide)
    (LossSum.empty _ _ _ _
      |>.append 6 0x2384dc4cc14 part0 |>.append 6 0x2384dc4cc14 part1 |>.append 6 0x237de8a4bdf part2 |>.append 6 0x23208029ffe part3
      |>.append 6 0x224f195b4d9 part4 |>.append 6 0x20c4ecf6d63 part5 |>.append 6 0x1e1548cb9db part6 |>.append 6 0x19d80883dd8 part7
      |>.append 6 0x1397af167d0 part8 |>.append 6 0xbd5d61b432 part9 |>.append 6 0x5ae1153f0f part10 |>.append 3 0x1573d9ca8a part11)

def receipt : KoalaSplitProof.Receipt envelope split unit :=
  ⟨terminal, plain, boxes, powers, plainPowers, tailPowers, 20829598565263,
    by decide,by decide,loss_bound,fun _ h h' => prices h h', tail⟩

end KoalaAt2428Gate30

#print axioms KoalaAt2428Gate30.loss_bound
#print axioms KoalaAt2428Gate30.receipt
