import ProximityPrize.SubmissionLower.KoalaGateSharedData
import ProximityPrize.SubmissionLower.FadicRisingGate
import ProximityPrize.SubmissionLower.KoalaSplitGateWords

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000

set_option linter.defProp false

namespace KoalaAt2428Gate60
open KoalaGateSharedData
open FadicGate KoalaGateCheck
open KoalaWeightedRate (Envelope)
open KoalaFarBridge (rowCheck plainCheck)

def envelope : Envelope :=
  ⟨132,53,3,135,53,3432,4435,⟨8665961308,50440861411,11805797951⟩,3783158159867⟩
abbrev split:ℕ:=48
abbrev unit:ℕ:=1919967379200
abbrev terminal:ℕ:=65
abbrev gate:=KoalaSplitRow.rate envelope split unit

private def boxesTape : List (List Entry) := [
  b05l,b04u,b03z,b033,b035,b023,b00w,b00y,
  bzv,bys,bxc,bxb,bvt,bvs,buc,bu9,
  bua,bt0,bsy,bs2,bqz,bpu,bol,bn5,
  bll,blk,bk3,bk2,big,bie,bfm,bfj,
  bbb,bbe,b5p,b59,b4u,b4w,b4y,b50,
  b51,b52,b53,b54,b55,b56,b57]
def boxes (r : ℕ) : List FadicGate.Entry :=
  if r < 18 then [] else boxesTape.getD (r-18) []

def plain : ℕ → ℕ × ℕ × ℕ
  | _ => (0,0,0)

private def powersTape : List String := [
  "","","","","","","","",
  "","","","","","","","",
  "","","!#","!#&","!#%+","!#&)",z3O,z2Q,
  z4a,z3g,"!#%)-18E","!#%'-29GE","!#$(+2:AG","!#%(+3;:II","!#$',/6;JI","!#$',/4<LJX",
  "!#$'*/4=FLP","!#$&*05>?NL","!#$'*06?>ON`","!#$'+-6:?QOW","!#$&)-26@KQOp","!#$&).17AESQg{","!#$&).28BAUS_~#!{","!#$&*.28CBVUUv~#!{",
  "!#$&(,39>CPVUn~#%~#!{","!#$&(,3:9DJXVf~#)~#%~#!{","!#$%),/5:EDZX^}~#)~#%~#!","!#$&),/3:FE[ZXu~#,~#)~#%|","!##&(-04;GFU[Zm~#0~#,~#)~#%","!#$%(+04;BGO^[d~#'~#0~#,~#)|","!##%(+05<=HI`^[|~#3~#0~#,~#)","!##%(+15=<IHb`^t~#7~#3~#0~#,|",
  "!!#%'+-69=JIZb`l~#.~#7~#3~#0~#*","!!#%'+.26=KJTcbc~#&~#:~#7~#3~#0|","!!#%'*.16>FKNecb{~#>~#:~#7~#3~#*","!!#%(*.27?ALKgecr~#6~#>~#:~#6~#2|","!!#%'*.27??MLagej~#-~#B~#>~#9~#3~#&","!!#%'*/28@?NMYige~#%~#E~#A~#=~#3~#&","!!#%'*,38<@ONSjify~#<~#D~#?~#3~#&","!!#%'),398AJONljfi~#3~#H~#?~#3~#&",
  "!!#%&)-059AEPOfkfb~#!~#K~#?~#3~#&","!!#$&)-/39BAQO]kfbn~#9~#?~#3~#&","!!#$')-049CBQOSkfb]~#(~#?~#3~#&","!!#$'*-04:CBQOLkfb]s~#?~#3~#&","!!#$&(+04:>BKOLbfb]b~#-~#3~#&","!!#$&(+04:9BDOLWfb]Wy~#3~#&","!!#$&)+14:9B@OLNfb]Wg~#3~#&","!!#$&),.469B@OLJfb]WU~!~~#&"]

def powers (r : ℕ) : List ℕ :=
  if r=0 then [] else KoalaSplitGateWords.powers (powersTape.getD (r-1) "")

def plainPowers : ℕ → List ℕ
  | _ => []

def tailPowers : List ℕ := KoalaSplitGateWords.powers "!!#$&),.149BAPMK_d`ZUu~#/~##ui]QE9."

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
private def part2 := checkPart 12 6 0x23825714916
private def part3 := checkPart 18 6 0x232c13aff78
private def part4 := checkPart 24 6 0x225afe1a9a0
private def part5 := checkPart 30 6 0x20dcd8c3382
private def part6 := checkPart 36 6 0x1e3ad02de60
private def part7 := checkPart 42 6 0x1a17097b922
private def part8 := checkPart 48 6 0x1408c708a07
private def part9 := checkPart 54 6 0xcb0b0d70bf
private def part10 := checkPart 60 4 0x50b6c60248

theorem loss_bound (N : ℕ) : Bound envelope terminal plain boxes 20823805153896 N :=
  loss_of_chunks 16 envelope terminal plain boxes 20823805153896 N (by decide) (by decide)
    (LossSum.empty _ _ _ _
      |>.append 6 0x2384dc4cc14 part0 |>.append 6 0x2384dc4cc14 part1 |>.append 6 0x23825714916 part2 |>.append 6 0x232c13aff78 part3
      |>.append 6 0x225afe1a9a0 part4 |>.append 6 0x20dcd8c3382 part5 |>.append 6 0x1e3ad02de60 part6 |>.append 6 0x1a17097b922 part7
      |>.append 6 0x1408c708a07 part8 |>.append 6 0xcb0b0d70bf part9 |>.append 4 0x50b6c60248 part10)

def receipt : KoalaSplitProof.Receipt envelope split unit :=
  ⟨terminal, plain, boxes, powers, plainPowers, tailPowers, 20823805153896,
    by decide,by decide,loss_bound,fun _ h h' => prices h h', tail⟩

end KoalaAt2428Gate60

#print axioms KoalaAt2428Gate60.loss_bound
#print axioms KoalaAt2428Gate60.receipt
