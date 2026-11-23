import ProximityPrize.SubmissionLower.KoalaGateSharedData
import ProximityPrize.SubmissionLower.FadicRisingGate
import ProximityPrize.SubmissionLower.KoalaSplitGateWords

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000

set_option linter.defProp false

namespace KoalaAt2428Gate46
open KoalaGateSharedData
open FadicGate KoalaGateCheck
open KoalaWeightedRate (Envelope)
open KoalaFarBridge (rowCheck plainCheck)

def envelope : Envelope :=
  ⟨128,54,3,131,54,3328,4431,⟨9140930045,49715535986,10822265925⟩,3833498757729⟩
abbrev split:ℕ:=48
abbrev unit:ℕ:=1919967636480
abbrev terminal:ℕ:=65
abbrev gate:=KoalaSplitRow.rate envelope split unit

private def boxesTape : List (List Entry) := [
  b05l,b04u,b03z,b043,b035,b023,b00w,b00y,
  bzv,bzx,byt,bxb,bvt,bvs,bvv,bu9,
  bua,bt0,bsy,bs2,bs1,br1,bpx,bor,
  bn9,blk,bln,bk2,big,bie,bfm,bfj,
  bbb,bbf,bbd,b5q,b5c,b5d,b5e,b5f,
  b5g,b5h,b5i,b5a,b5b,b5j,b5t]
def boxes (r : ℕ) : List FadicGate.Entry :=
  if r < 18 then [] else boxesTape.getD (r-18) []

def plain : ℕ → ℕ × ℕ × ℕ
  | _ => (0,0,0)

private def powersTape : List String := [
  "","","","","","","","",
  "","","","","","","","",
  "","","!#","!#&","!#&","!#&)",z3O,z2Q,
  z4a,z3g,"!#%)-18","!#%'.29G","!#$(+2:AG","!#%(+3;:II","!#$',/6;JI","!#$',/4<LJ",
  "!#$'*/4=FLP","!#$&*05>@NL","!#$'*06?>PNa","!#$'+-6:?QPX","!#$&)-26@KQPp","!#$&).17AESQh","!#$&).28BAUS_~##","!#$&*.28CBWUVw~##",
  "!#$&(,39>CPWUo~#&~##","!#$&),3:9DJXWg~#*~#&~##","!#$%),05:EDZX^~!~~#*~#&~##","!#$&),/4:FE]ZXv~#-~#*~#&","!##&(-04;GFV]Zn~#1~#-~#*~#&","!#$%(+04<BGO_]e~#(~#1~#-~#*}","!##%(+05<=HI`_]}~#4~#1~#-~#*","!##%(+15=<IHb`_u~#8~#4~#1~#-}",
  "!!#%'+.69=JI[b`l~#0~#8~#4~#1~#+","!!#%'+.26>KJTdbd~#'~#;~#8~#4~#1}","!!#%'*.16>FKNedb|~#?~#;~#8~#4~#+","!!#%(*.27?ALKgeds~#7~#?~#;~#8~#4","!!#%'*.27@?MLagek~#.~#C~#?~#;~#5~#)","!!#%'*/28@@NMZige~#&~#F~#C~#?~#5~#)","!!#%'*,38<@ONTkig{~#>~#F~#A~#5~#)","!!#%'),398AJONmkgk~#5~#J~#A~#5~#)",
  "!!#%&)-059BEPOflgb~#%~#M~#A~#5~#)","!!#$&)-/39BBQO^lgbp~#<~#A~#5~#)","!!#$')-049CBROSlgb^~#*~#A~#5~#)","!!#$'*-04:DBROMlgb^u~#A~#5~#)","!!#$&(+04:>BKOMbgb^d~#0~#5~#)","!!#$&(+15:9BEOMXgb^X{~#5~#)","!!#$&),15:9B@OMNgb^Xi~#5~#)","!!#$&),.569B@OMJgb^XW~##~#)"]

def powers (r : ℕ) : List ℕ :=
  if r=0 then [] else KoalaSplitGateWords.powers (powersTape.getD (r-1) "")

def plainPowers : ℕ → List ℕ
  | _ => []

def tailPowers : List ℕ := KoalaSplitGateWords.powers "!!#$&),.149BAPMK_d_ZUt~#/~##th[OD8,"

def priced (r:ℕ):Bool:=rowCheck gate r (boxes r) (powers r) (plain r) (plainPowers r)
private theorem priced_list : (List.range 64).all (fun i => priced (i+1)) = true := by decide +kernel

theorem prices {r : ℕ} (hr : 0 < r) (hR : r < terminal) : priced r = true :=
  price hr hR priced_list

theorem tail:plainCheck gate terminal (4012,1650,550) tailPowers=true:=by decide +kernel

private abbrev Chunk (i n v : ℕ) := lossChunk 16 envelope plain boxes i n = v
private theorem checkPart (i n v : ℕ) (ok : Chunk i n v := by
    unfold Chunk
    rw [← KoalaGateCheck.lossChunkRising_eq]
    decide +kernel) : Chunk i n v := ok
private def part0 := checkPart 0 6 0x2384dc4cc14
private def part1 := checkPart 6 6 0x2384dc4cc14
private def part2 := checkPart 12 6 0x23825470687
private def part3 := checkPart 18 6 0x232e0676e4e
private def part4 := checkPart 24 6 0x225e37e6503
private def part5 := checkPart 30 6 0x20dc2f42ae4
private def part6 := checkPart 36 6 0x1e40467b9ac
private def part7 := checkPart 42 6 0x1a0e64dac99
private def part8 := checkPart 48 6 0x13f84abde0e
private def part9 := checkPart 54 6 0xc8ea75125c
private def part10 := checkPart 60 4 0x4ec7b39ea7

theorem loss_bound (N : ℕ) : Bound envelope terminal plain boxes 20802291667514 N :=
  loss_of_chunks 16 envelope terminal plain boxes 20802291667514 N (by decide) (by decide)
    (LossSum.empty _ _ _ _
      |>.append 6 0x2384dc4cc14 part0 |>.append 6 0x2384dc4cc14 part1 |>.append 6 0x23825470687 part2 |>.append 6 0x232e0676e4e part3
      |>.append 6 0x225e37e6503 part4 |>.append 6 0x20dc2f42ae4 part5 |>.append 6 0x1e40467b9ac part6 |>.append 6 0x1a0e64dac99 part7
      |>.append 6 0x13f84abde0e part8 |>.append 6 0xc8ea75125c part9 |>.append 4 0x4ec7b39ea7 part10)

def receipt : KoalaSplitProof.Receipt envelope split unit :=
  ⟨terminal, plain, boxes, powers, plainPowers, tailPowers, 20802291667514,
    by decide,by decide,loss_bound,fun _ h h' => prices h h', tail⟩

end KoalaAt2428Gate46

#print axioms KoalaAt2428Gate46.loss_bound
#print axioms KoalaAt2428Gate46.receipt
