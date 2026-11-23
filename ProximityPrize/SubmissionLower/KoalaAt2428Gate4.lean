import ProximityPrize.SubmissionLower.KoalaGateSharedData
import ProximityPrize.SubmissionLower.KoalaGateChunkSums
import ProximityPrize.SubmissionLower.KoalaSplitGateWords

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000

set_option linter.defProp false

namespace KoalaAt2428Gate4
open KoalaGateSharedData
open FadicGate KoalaGateCheck
open KoalaWeightedRate (Envelope)
open KoalaFarBridge (rowCheck plainCheck)

def envelope : Envelope :=
  ⟨112,56,9,115,56,2912,4340,⟨10157268071,43330555563,10165879768⟩,3582613312454⟩
abbrev split:ℕ:=32
abbrev unit:ℕ:=1920000000000
abbrev terminal:ℕ:=62
abbrev gate:=KoalaSplitRow.rate envelope split unit

private def boxesTape : List (List Entry) := [
  b04y,b044,b042,b036,b025,b011,b00x,bzy,
  bzw,byp,byq,bxe,bvw,bua,bub,bsy,
  bsz,bs1,brz,bs0,bqx,bqw,bps,bon,
  bn8,blo,bk6,bifAtom,bii,bfl,bfk,bbi,
  bbg,bbh,bbl,bbn,bbp,bbr,bbt,bbu,
  bbw]
def boxes (r : ℕ) : List FadicGate.Entry :=
  if r < 21 then [] else boxesTape.getD (r-21) []

def plain : ℕ → ℕ × ℕ × ℕ
  | _ => (0,0,0)

private def powersTape : List String := [
  "","","","","","","","",
  "","","","","","","","",
  "","","","","!#","!#%","!#%","!#%)",
  "!#$'+","!#$'+0","!#$(,/","!#$',07","!#$'*17","!#$'*187","!#$&*-38","!#$&+-29H",
  "!!$&).2:BH","!!$&).3;;JH","!!$&)/4<;KJ","!!$&),47<MKN","!!#%(,04=FMK","!!#%(,/5>@NM^","!!#%(,05?>PNT","!!#%(-06@?RPN",
  "!!#%'*16;@KRPd","!!#%'+176AESR[","!!#%(+-37AAUSRt","!!#%(+.18BAVUSk~#!","!!#%'+.28CBPVUb~#&~#!","!!#$').29>CJXVXz~#&~#!","!!#%').399DCYXVq~#)~#&~#!","!!#%'*/3:9ED[YXh~#,~#)~#&~#!",
  "!!#$&*,36:FEU[Y`~##~#,~#)~#&",z4x,"!!#$&(,/4;BGH_^[o~#2~#/~#,~#)","!!#$&),04<=HGa_^f~#*~#2~#/~#,~#&","!!#$&)-05<<IHYa_]~!~~#5~#2~#/~#&","!!#$&)-05=<JISba_u~#8~#5~#0~#&","!!#$&)+059=KJLdb_j~#0~#8~#1~#&","!!#$&(+165=EKIec_Z~#%~#;~#1~#&",
  "!!#$%(+.26>@KJ^d_Zq~#<~#1~#&","!!#$%(+.16?>LJTd_Z`~#+~#1~#&","!!#$&(+.17?>LJKd_ZVw~#1~#&","!!#$&(+.27@>LJHd_ZVf~#1~#&","!!#$%'*.27:>FJHY_ZVT}~#&"]
def powers (r : ℕ) : List ℕ :=
  if r=0 then [] else KoalaSplitGateWords.powers (powersTape.getD (r-1) "")

def plainPowers : ℕ → List ℕ
  | _ => []

def tailPowers:List ℕ:=KoalaSplitGateWords.powers "!!#$%'*/287?ALISc_ZVw~#2~#(zpfZPF;"

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
private def part3 := checkPart 18 6 0x235038637e5
private def part4 := checkPart 24 6 0x2280831fa8b
private def part5 := checkPart 30 6 0x2107c8d6014
private def part6 := checkPart 36 6 0x1e909a85ad2
private def part7 := checkPart 42 6 0x1a911fc03c1
private def part8 := checkPart 48 6 0x14ab6aedc60
private def part9 := checkPart 54 6 0xdb8e5454ce
private def part10 := checkPart 60 1 0x1b2e03fc60

theorem loss_bound (N : ℕ) : Bound envelope terminal plain boxes 20796235809505 N :=
  loss_of_chunks 32 envelope terminal plain boxes 20796235809505 N (by decide) (by decide)
    (LossSum.empty _ _ _ _
      |>.append 6 0x2384dc4cc14 part0 |>.append 6 0x2384dc4cc14 part1 |>.append 6 0x2384dc4cc14 part2 |>.append 6 0x235038637e5 part3
      |>.append 6 0x2280831fa8b part4 |>.append 6 0x2107c8d6014 part5 |>.append 6 0x1e909a85ad2 part6 |>.append 6 0x1a911fc03c1 part7
      |>.append 6 0x14ab6aedc60 part8 |>.append 6 0xdb8e5454ce part9 |>.append 1 0x1b2e03fc60 part10)

def receipt : KoalaSplitProof.Receipt envelope split unit :=
  ⟨terminal, plain, boxes, powers, plainPowers, tailPowers, 20796235809505,
    by decide,by decide,loss_bound,fun _ h h' => prices h h', tail⟩

end KoalaAt2428Gate4

#print axioms KoalaAt2428Gate4.loss_bound
#print axioms KoalaAt2428Gate4.receipt
