import ProximityPrize.SubmissionLower.KoalaGateSharedData
import ProximityPrize.SubmissionLower.KoalaGateChunkSums
import ProximityPrize.SubmissionLower.KoalaSplitGateWords

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000

set_option linter.defProp false

namespace KoalaAt2428Gate54
open KoalaGateSharedData
open FadicGate KoalaGateCheck
open KoalaWeightedRate (Envelope)
open KoalaFarBridge (rowCheck plainCheck)

def envelope : Envelope :=
  ⟨116,55,6,119,55,3016,4419,⟨9614974980,44441443751,10352345727⟩,3560290250632⟩
abbrev split:ℕ:=48
abbrev unit:ℕ:=1919967989760
abbrev terminal:ℕ:=62
abbrev gate:=KoalaSplitRow.rate envelope split unit

private def boxesTape : List (List Entry) := [
  b05p,b04y,b044,b042,b036,b025,b011,b00x,
  bzy,bzw,byp,bxj,bvv,bvw,bua,bub,
  bsy,bsz,bs1,brz,br0,bqx,bqw,bps,
  bon,bn8,blo,bk6,bifAtom,bii,bfl,bfk,
  bbd,bbj,bbk,bbm,bbo,bbq,bbs,bc2,
  bc3,b5a.take 22]
def boxes (r : ℕ) : List FadicGate.Entry :=
  if r < 20 then [] else boxesTape.getD (r-20) []

def plain : ℕ → ℕ × ℕ × ℕ
  | _ => (0,0,0)

private def powersTape : List String := [
  "","","","","","","","",
  "","","","","","","","",
  "","","","","!#","!#%","!#%","!#%)",
  z57,"!#%(,1","!#%(,0",z4H,"!#$'*18","!#$(+298","!#$'+.49H","!#$'+.3:IH",
  "!#$')/3;CI","!#$&*/4<=KI",z62,"!#$&*,58=NMP","!#$&)-15>HNM","!#$&)-06?BPN`","!#$&)-16@?RPW","!#$&).17A@SROo",
  "!#$&(+28<AMSRg","!#$&(+288BGUS^","!#$%(,/48CBVUUv","!#$%(,/39DCXVUm~#%","!##%',/3:EDRXVe~#(~#%","!##%(*/3:@EKZX[|~#(~#%","!##%(*/4;;FE[ZXt~#+~#(~#%","!##%(+04;;GF^[Zk~#.~#+~#(~#%",
  "!!#%'+-57;HGW^[c~#&~#.~#+~#(","!!#%'+-15<IHP`^[z~#2~#.~#+~#(","!!#%')-05=DIJa`^r~#5~#2~#.~#+","!!#%'*.16=?JIca`i~#,~#5~#2~#.~#+","!!#%'*.16>=KJ]ca`~#$~#8~#5~#1~#,","!!#%'*.16?>LKUdcax~#;~#8~#5~#,","!!#$'*,27:?MLOfdbo~#3~#;~#7~#,","!!#$'),277?GLKhfb`~#*~#>~#7~#,",
  "!!#%&),/47@BMLagb^w~#B~#7~#,","!!#$&),/28@@NLXgb^f~#1~#7~#,","!!#$&),/38A@OLNgb^Y}~#7~#,","!!#$&)-/39B@OLJgb^Yl~#7~#,","!!#$&(+/39<@HLJ^b^YY~#&~#,"]

def powers (r : ℕ) : List ℕ :=
  if r=0 then [] else KoalaSplitGateWords.powers (powersTape.getD (r-1) "")

def plainPowers : ℕ → List ℕ
  | _ => []

def tailPowers : List ℕ := KoalaSplitGateWords.powers "!!#$&(+0498ACNKVea]Wz~#5~#*|rg]QF<1"

def priced (r:ℕ):Bool:=rowCheck gate r (boxes r) (powers r) (plain r) (plainPowers r)
private theorem priced_list : (List.range 61).all (fun i => priced (i+1)) = true := by decide +kernel

theorem prices {r : ℕ} (hr : 0 < r) (hR : r < terminal) : priced r = true :=
  price hr hR priced_list

theorem tail:plainCheck gate terminal (4012,1650,550) tailPowers=true:=by decide +kernel

private abbrev Chunk (i n v : ℕ) := lossChunk 32 envelope plain boxes i n = v
private theorem checkPart (i n v : ℕ) (ok : Chunk i n v := by decide +kernel) : Chunk i n v := ok
private def part0 := checkPart 0 6 0x2384dc4cc14
private def part1 := checkPart 6 6 0x2384dc4cc14
private def part2 := checkPart 12 6 0x2384dc4cc14
private def part3 := checkPart 18 6 0x234d23a2aa1
private def part4 := checkPart 24 6 0x2281f5a6778
private def part5 := checkPart 30 6 0x2104c6b2833
private def part6 := checkPart 36 6 0x1e949784767
private def part7 := checkPart 42 6 0x1a9e8ad657b
private def part8 := checkPart 48 6 0x14c2142c986
private def part9 := checkPart 54 6 0xdc8842793c
private def part10 := checkPart 60 1 0x1b376980b4

theorem loss_bound (N : ℕ) : Bound envelope terminal plain boxes 20810096086752 N :=
  loss_of_chunks 32 envelope terminal plain boxes 20810096086752 N (by decide) (by decide)
    (LossSum.empty _ _ _ _
      |>.append 6 0x2384dc4cc14 part0 |>.append 6 0x2384dc4cc14 part1 |>.append 6 0x2384dc4cc14 part2 |>.append 6 0x234d23a2aa1 part3
      |>.append 6 0x2281f5a6778 part4 |>.append 6 0x2104c6b2833 part5 |>.append 6 0x1e949784767 part6 |>.append 6 0x1a9e8ad657b part7
      |>.append 6 0x14c2142c986 part8 |>.append 6 0xdc8842793c part9 |>.append 1 0x1b376980b4 part10)

def receipt : KoalaSplitProof.Receipt envelope split unit :=
  ⟨terminal, plain, boxes, powers, plainPowers, tailPowers, 20810096086752,
    by decide,by decide,loss_bound,fun _ h h' => prices h h', tail⟩

end KoalaAt2428Gate54

#print axioms KoalaAt2428Gate54.loss_bound
#print axioms KoalaAt2428Gate54.receipt
