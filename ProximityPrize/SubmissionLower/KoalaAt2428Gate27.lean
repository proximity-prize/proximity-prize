import ProximityPrize.SubmissionLower.KoalaAt2428Gate26
import ProximityPrize.SubmissionLower.KoalaGateSharedData
import ProximityPrize.SubmissionLower.KoalaGateChunkSums
import ProximityPrize.SubmissionLower.KoalaSplitGateWords

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000

set_option linter.defProp false

namespace KoalaAt2428Gate27
open KoalaGateSharedData
open FadicGate KoalaGateCheck
open KoalaWeightedRate (Envelope)
open KoalaFarBridge (rowCheck plainCheck)

def envelope : Envelope :=
  ⟨132,56,4,135,56,3432,4435,⟨8009697488,34821181150,80356312802⟩,3400959941111⟩
abbrev split:ℕ:=48
abbrev unit:ℕ:=1919967423360
abbrev terminal:ℕ:=70
abbrev gate:=KoalaSplitRow.rate envelope split unit

private def boxesTape : List (List Entry) := [
  b05l,b04u,b03z,b033,b035,b023,b00w,b00y,
  bzv,bzx,byt,bxb,bvt,bvs,buc,bu9,
  bua,bt0,bsy,bs2,bs1,br1,bol,bn5,
  bll,blk,bk3,bk2,big,bie,bfm,bfj,
  bbb,bbe,b6y,b7i,b7x,b87,b8k,b8t,
  b95,b9b,b9n,b9t,ba6,bac,bam,b0o.take 5++unpack 18 0x3e2449f1224f89127c4893e2449f4a93e048d60a5ac,
  b3y.take 23,bq.take 23,bs.take 23,bt.take 23]
def boxes (r : ℕ) : List FadicGate.Entry :=
  if r < 18 then [] else boxesTape.getD (r-18) []

def plain : ℕ → ℕ × ℕ × ℕ
  | _ => (0,0,0)

private def powersTape : List String := [
  "","","","","","","","",
  "","","","","","","","",
  "","","!#","!#&","!#&+","!#&)",z3O,z2Q,
  z4a,z3g,"!#%)-18","!#%(.29G",z6Y,"!#%(+3;;II",z48,"!#$',/4<LKX",
  "!#$'*05=FLQ","!#$'*05>@NL","!#$'+16?>PN`","!#$'+-7;?RPW","!#$&).37ALRPo","!#$&).27BFSRg","!#$&*.28CBUS_}","!#$&*/39DCWUWu}z",
  "!#$&),3:?DQWUn~##}z","!#$&),3::EKYWg~#'~##}z","!#$&),06:FE[Y_}~#'~##}","!#$&)-04;GF][Yu~#+~#'~##{","!#$&(-04<HGV][m~#.~#+~#'~##","!#$%(+05<CHP_]e~#'~#.~#+~#'{","!##%(+15=>IJa_^|~#2~#.~#+~#'","!##%(+16>=JIca_u~#5~#2~#.~#+{",
  "!!#%'+.6:>KJ]cam~#-~#5~#2~#.~#)","!!#%',.36>LKVdcf~#&~#8~#5~#2~#.{","!!#%(*.27?GLPfdc|~#<~#8~#5~#2~#)","!!#%(*/27@BMLhfdt~#5~#<~#8~#4~#/{","!!#%'*/28@@NMbhfm~#-~#@~#<~#8~#2~#%","!!#%'*/38A@ON[jhf~#&~#C~#@~#:~#2~#%","!!#%'+-39=APOUljiz~#;~#C~#?~#2~#%","!!#%')-399BKPOnkin~#2~#F~#?~#2~#%",
  "!!#%')-069CGQQgnid~#&~#K~#?~#2~#%","!!#$')-04:CBRQanidr~#:~#?~#2~#%","!!#$'*-04:DDTQVnida~#*~#?~#2~#%","!!#%'*.05;EDTQNnid_v~#?~#2~#%","!!#$&),15<@DMQNeid_e~#.~#2~#%","!!#$&),16<;DGQN[id_Yz~#2~#%","!!#$&),26<:DBQNQid_Yi~#2~#%","!!#$&),/67:DBQNLid_YX~!~~#%",
  "!!#$&),.25:DBQNL`d_YSn~#%","!!#$&(,.15:DBKNLUd_YS]~#%","!!#$&(*.15:>BDNLLd_YSNr","!!#$&(*.15:9B@NLId_YSNa","!!#$&(*.15:9B@NLIY_YSNO"]

def powers (r : ℕ) : List ℕ :=
  if r=0 then [] else KoalaSplitGateWords.powers (powersTape.getD (r-1) "")

def plainPowers : ℕ → List ℕ
  | _ => []

def tailPowers : List ℕ := KoalaSplitGateWords.powers "!!#$&(*.15:9B@OLIQ_YTOJfk^QD8+"

def priced (r:ℕ):Bool:=rowCheck gate r (boxes r) (powers r) (plain r) (plainPowers r)
private theorem priced_list : (List.range 69).all (fun i => priced (i+1)) = true := by decide +kernel

theorem prices {r : ℕ} (hr : 0 < r) (hR : r < terminal) : priced r = true :=
  price hr hR priced_list

theorem tail:plainCheck gate terminal (4012,1650,550) tailPowers=true:=by decide +kernel

private abbrev Chunk (i n v : ℕ) := lossChunk 12 envelope plain boxes i n = v
private theorem checkPart (i n v : ℕ) (ok : Chunk i n v := by decide +kernel) : Chunk i n v := ok
private def part0 := checkPart 0 6 0x2384dc4cc14
private def part1 := checkPart 6 6 0x2384dc4cc14
private def part2 := checkPart 12 6 0x23823b4cf05
private def part3 := checkPart 18 6 0x23282b5aa64
private def part4 := checkPart 24 6 0x2252406a077
private def part5 := checkPart 30 6 0x20bd8b1fdf2
private def part6 := checkPart 36 6 0x1e006802399
private def part7 := checkPart 42 6 0x19a51dab139
private def part8 := checkPart 48 6 0x134dfa90aeb
private def part9 := checkPart 54 6 0xbbdcdda320
private def part10 := checkPart 60 6 0x5b37a6614a
private def part11 := checkPart 66 3 0x159eb96dea

theorem loss_bound (N : ℕ) : Bound envelope terminal plain boxes 20788345176587 N :=
  loss_of_chunks 12 envelope terminal plain boxes 20788345176587 N (by decide) (by decide)
    (LossSum.empty _ _ _ _
      |>.append 6 0x2384dc4cc14 part0 |>.append 6 0x2384dc4cc14 part1 |>.append 6 0x23823b4cf05 part2 |>.append 6 0x23282b5aa64 part3
      |>.append 6 0x2252406a077 part4 |>.append 6 0x20bd8b1fdf2 part5 |>.append 6 0x1e006802399 part6 |>.append 6 0x19a51dab139 part7
      |>.append 6 0x134dfa90aeb part8 |>.append 6 0xbbdcdda320 part9 |>.append 6 0x5b37a6614a part10 |>.append 3 0x159eb96dea part11)

def receipt : KoalaSplitProof.Receipt envelope split unit :=
  ⟨terminal, plain, boxes, powers, plainPowers, tailPowers, 20788345176587,
    by decide,by decide,loss_bound,fun _ h h' => prices h h', tail⟩

end KoalaAt2428Gate27

#print axioms KoalaAt2428Gate27.loss_bound
#print axioms KoalaAt2428Gate27.receipt
