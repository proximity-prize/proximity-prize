import ProximityPrize.SubmissionLower.KoalaGateSharedData
import ProximityPrize.SubmissionLower.KoalaGateChunkSums
import ProximityPrize.SubmissionLower.KoalaSplitGateWords

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000

set_option linter.defProp false

namespace KoalaAt2428Gate35
open KoalaGateSharedData
open FadicGate KoalaGateCheck
open KoalaWeightedRate (Envelope)
open KoalaFarBridge (rowCheck plainCheck)

def envelope : Envelope :=
  ⟨132,55,4,135,55,3432,4435,⟨7643543872,34232809826,75955682219⟩,3260075083079⟩
abbrev split:ℕ:=48
abbrev unit:ℕ:=1919967496320
abbrev terminal:ℕ:=68
abbrev gate:=KoalaSplitRow.rate envelope split unit

private def boxesTape : List (List Entry) := [
  b05l,b04u,b03z,b033,b035,b023,b00w,b00y,
  bzv,bzx,byt,bxb,bvt,bvs,buc,bu9,
  bua,bt0,bsy,bs2,bs1,br1,bol,bn5,
  bll,blk,bk3,bk2,big,bie,bfm,bfj,
  bbb,bbe,b5p,b59,b4u,b4w,b4y,b50,
  b51,b52,b53,b54,b55,b56,b57,b5k,
  b5n,b64]
def boxes (r : ℕ) : List FadicGate.Entry :=
  if r < 18 then [] else boxesTape.getD (r-18) []

def plain : ℕ → ℕ × ℕ × ℕ
  | _ => (0,0,0)

private def powersTape : List String := [
  "","","","","","","","",
  "","","","","","","","",
  "","","!#","!#&","!#%+","!#&)",z3O,z4D,
  "!#%(,6",z4I,"!#%)-17","!#%'-18E","!#$(+29@E","!#%(+3:9GF","!#$'+/5:IG","!#$',/3;KIT",
  "!#$'*/4<EKL","!#$&*05=>LK","!#$'*05>=NL[","!#$'+-69>PNS","!#$&)-26?JPNj","!#$&)-17@DQPb","!#$&).27A@SQYy","!#$&*.28BAUSRqyu",
  "!#$&(,29=BOUSi|yu","!#$&(,399CIWUa~#!|yu","!#$%),/59DCXWYx~#!|y","!#$%),/3:EDZXWp~#&~#!|w","!##&(-/4;FETZXh~#)~#&~#!|","!#$%(+04;AFN]Z`~!~~#)~#&~#!w","!##%(+05<=GH^]Zv~#,~#)~#&~#!","!##%(+05=<HG`^]o~#/~#,~#)~#&w",
  "!!#%'+-68=IHY`^g~#(~#/~#,~#)~#$","!!#%'+.26=JISb`_}~#3~#/~#,~#)w","!!#%'*.16>EJMcb`u~#6~#3~#/~#,~#$","!!#%(*.27?AKJecbn~#.~#6~#3~#/~#,v","!!#%'*.27??LK_ecf~#'~#:~#6~#2~#0~#$","!!#%'*/27@?MLXged|~#=~#9~#6~#0~#$","!!#%'*,38<@NMRiggt~#5~#<~#<~#0~#$","!!#%'),388AJONkigj~#-~#@~#<~#0~#$",
  "!!#%&)-058AEPPelgb~#!~#F~#<~#0~#$","!!#$&)-/39BAQP^lgbn~#7~#<~#0~#$","!!#$')-049CCRPTlgb^~#&~#<~#0~#$","!!#$'*-04:DCRPMlgb]s~#<~#0~#$","!!#$&(+04;?CLPMcgb]c~#+~#0~#$","!!#$&(+15;:CEPMXgb]Wx~#0~#$","!!#$&),15;:CAPMOgb]Wg~#0~#$","!!#$&),.57:CAPMJgb]WV|~#$",
  "!!#$&),.14:CAPMJ^b]WSl~#$","!!#$&(,.04:CAIMJTb]WS[~#$","!!#$&(*.04:=ACMJJb]WSNp"]

def powers (r : ℕ) : List ℕ :=
  if r=0 then [] else KoalaSplitGateWords.powers (powersTape.getD (r-1) "")

def plainPowers : ℕ → List ℕ
  | _ => []

def tailPowers : List ℕ := KoalaSplitGateWords.powers "!!#$&(*.04:9A?MKHc^XSNawk_RG;/$"

def priced (r:ℕ):Bool:=rowCheck gate r (boxes r) (powers r) (plain r) (plainPowers r)
private theorem priced_list : (List.range 67).all (fun i => priced (i+1)) = true := by decide +kernel

theorem prices {r : ℕ} (hr : 0 < r) (hR : r < terminal) : priced r = true :=
  price hr hR priced_list

theorem tail:plainCheck gate terminal (4012,1650,550) tailPowers=true:=by decide +kernel

private abbrev Chunk (i n v : ℕ) := lossChunk 16 envelope plain boxes i n = v
private theorem checkPart (i n v : ℕ) (ok : Chunk i n v := by decide +kernel) : Chunk i n v := ok
private def part0 := checkPart 0 6 0x2384dc4cc14
private def part1 := checkPart 6 6 0x2384dc4cc14
private def part2 := checkPart 12 6 0x2382486cf98
private def part3 := checkPart 18 6 0x2329ffcd1a1
private def part4 := checkPart 24 6 0x22586807938
private def part5 := checkPart 30 6 0x20cc015a33c
private def part6 := checkPart 36 6 0x1e1d62bea9a
private def part7 := checkPart 42 6 0x19d94fb6b59
private def part8 := checkPart 48 6 0x13a2577b958
private def part9 := checkPart 54 6 0xc1a11f61c4
private def part10 := checkPart 60 6 0x611d5e7747
private def part11 := checkPart 66 1 0x98d55c204

theorem loss_bound (N : ℕ) : Bound envelope terminal plain boxes 20837085610031 N :=
  loss_of_chunks 16 envelope terminal plain boxes 20837085610031 N (by decide) (by decide)
    (LossSum.empty _ _ _ _
      |>.append 6 0x2384dc4cc14 part0 |>.append 6 0x2384dc4cc14 part1 |>.append 6 0x2382486cf98 part2 |>.append 6 0x2329ffcd1a1 part3
      |>.append 6 0x22586807938 part4 |>.append 6 0x20cc015a33c part5 |>.append 6 0x1e1d62bea9a part6 |>.append 6 0x19d94fb6b59 part7
      |>.append 6 0x13a2577b958 part8 |>.append 6 0xc1a11f61c4 part9 |>.append 6 0x611d5e7747 part10 |>.append 1 0x98d55c204 part11)

def receipt : KoalaSplitProof.Receipt envelope split unit :=
  ⟨terminal, plain, boxes, powers, plainPowers, tailPowers, 20837085610031,
    by decide,by decide,loss_bound,fun _ h h' => prices h h', tail⟩

end KoalaAt2428Gate35

#print axioms KoalaAt2428Gate35.loss_bound
#print axioms KoalaAt2428Gate35.receipt
