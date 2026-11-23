import ProximityPrize.SubmissionLower.KoalaGateSharedData
import ProximityPrize.SubmissionLower.KoalaGateChunkSums
import ProximityPrize.SubmissionLower.KoalaSplitGateWords

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000

set_option linter.defProp false

namespace KoalaAt2428Gate6
open KoalaGateSharedData
open FadicGate KoalaGateCheck
open KoalaWeightedRate (Envelope)
open KoalaFarBridge (rowCheck plainCheck)

def envelope : Envelope :=
  ⟨112,56,13,115,56,2912,4340,⟨10177299998,43416011081,10185933055⟩,3589678859344⟩
abbrev split:ℕ:=32
abbrev unit:ℕ:=1920000000000
abbrev terminal:ℕ:=62
abbrev gate:=KoalaSplitRow.rate envelope split unit

private def boxesTape : List (List Entry) := [
  b05n,b04v,b042,b036,b025,b011,b00x,bzy,
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
  "","","","","","!#","!#%","!#%)",
  "!#$'+","!#$'+0","!#$(,/","!#$',07","!#$'*18","!#$'*188","!#$&*-38","!#$&+-29H",
  "!!$&).2:BH","!!$&).3;;JH","!!$&)/4<;KJ","!!$&),47<MKO","!!#%(,04=FMK","!!#%(,/5>@NM^","!!#%(,05?>PNU","!!#%(-06@?RPN",
  "!!#%'*16;@KRPe","!!#%'+176AESR[","!!#%(+-37BAUSSt","!!#%(+.18BBVUSk~##","!!#%'+.28CBPVUb~#&~##","!!#$').29>CJXVYz~#&~##","!!#%').399DCZXVq~#)~#&~##","!!#%'*/3:9ED[ZXi~#,~#)~#&~##",
  "!!#$&*,36:FEU[Z`~##~#,~#)~#&",z4x,"!!#$&(,/4;BGH_^[o~#3~#/~#,~#)","!!#$&),04<=HGa_^f~#*~#3~#/~#,~#&","!!#$&)-05<<IHYa_^~!~~#6~#3~#/~#'","!!#$&)-05=<JISba_u~#9~#6~#0~#'","!!#$&)+069=KJLdb`j~#0~#9~#1~#'","!!#$&(+165=FKIec`Z~#%~#;~#1~#'",
  "!!#$%(+.26>@KJ^d`Zr~#<~#1~#'","!!#$%(+.16?>LJUd`Za~#+~#1~#'","!!#$&(+.17?>LJKd`ZVx~#1~#'","!!#$&(+.27@>LJHd`ZVg~#1~#'","!!#$%'*.27;>FJHZ`ZVU~!~~#'"]
def powers (r : ℕ) : List ℕ :=
  if r=0 then [] else KoalaSplitGateWords.powers (powersTape.getD (r-1) "")

def plainPowers : ℕ → List ℕ
  | _ => []

def tailPowers:List ℕ:=KoalaSplitGateWords.powers "!!#$%(*/287?ALITc_ZVx~#2~#({pfZPF;"

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
private def part3 := checkPart 18 6 0x2356ec7f1e4
private def part4 := checkPart 24 6 0x228015956a6
private def part5 := checkPart 30 6 0x2106bb75115
private def part6 := checkPart 36 6 0x1e8e7638d31
private def part7 := checkPart 42 6 0x1a8d4fc20c3
private def part8 := checkPart 48 6 0x14a50c86dc4
private def part9 := checkPart 54 6 0xdb0f6a1843
private def part10 := checkPart 60 1 0x1b1ae81467

theorem loss_bound (N : ℕ) : Bound envelope terminal plain boxes 20791880140349 N :=
  loss_of_chunks 32 envelope terminal plain boxes 20791880140349 N (by decide) (by decide)
    (LossSum.empty _ _ _ _
      |>.append 6 0x2384dc4cc14 part0 |>.append 6 0x2384dc4cc14 part1 |>.append 6 0x2384dc4cc14 part2 |>.append 6 0x2356ec7f1e4 part3
      |>.append 6 0x228015956a6 part4 |>.append 6 0x2106bb75115 part5 |>.append 6 0x1e8e7638d31 part6 |>.append 6 0x1a8d4fc20c3 part7
      |>.append 6 0x14a50c86dc4 part8 |>.append 6 0xdb0f6a1843 part9 |>.append 1 0x1b1ae81467 part10)

def receipt : KoalaSplitProof.Receipt envelope split unit :=
  ⟨terminal, plain, boxes, powers, plainPowers, tailPowers, 20791880140349,
    by decide,by decide,loss_bound,fun _ h h' => prices h h', tail⟩

end KoalaAt2428Gate6

#print axioms KoalaAt2428Gate6.loss_bound
#print axioms KoalaAt2428Gate6.receipt
