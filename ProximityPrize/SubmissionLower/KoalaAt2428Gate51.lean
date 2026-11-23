import ProximityPrize.SubmissionLower.KoalaGateSharedData
import ProximityPrize.SubmissionLower.KoalaGateChunkSums
import ProximityPrize.SubmissionLower.KoalaSplitGateWords

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000

set_option linter.defProp false

namespace KoalaAt2428Gate51
open KoalaGateSharedData
open FadicGate KoalaGateCheck
open KoalaWeightedRate (Envelope)
open KoalaFarBridge (rowCheck plainCheck)

def envelope : Envelope :=
  ⟨132,55,2,135,55,3432,4435,⟨3928544319,15337142021,142518531724⟩,1608993387199⟩
abbrev split:ℕ:=48
abbrev unit:ℕ:=1919966432640
abbrev terminal:ℕ:=63
abbrev gate:=KoalaSplitRow.rate envelope split unit

private def boxesTape : List (List Entry) := [
  b05n,b04v,b042,b036,b025,b024,b00x,bzy,
  bzw,byp,byq,bxe,bvw,bua,bub,bsy,
  bsz,bs1,brz,bs0,bqx,bqw,bps,bpt,
  bou,bng,blq,bk7,bii,bfl,bfk,bbx,
  bc6,bc8,bby,bbz,bc0,bc1,b2k.take 22,b2r.take 22,
  b2w.take 22,b34.take 22]
def boxes (r : ℕ) : List FadicGate.Entry :=
  if r < 21 then [] else boxesTape.getD (r-21) []

def plain : ℕ → ℕ × ℕ × ℕ
  | _ => (0,0,0)

private def powersTape : List String := [
  "","","","","","","","",
  "","","","","","","","",
  "","","","","","!#","!#%","!#%)",
  z3p,"!#%(+","!#$(+/","!#$',/5",z65,"!#$'*066","!#$&*-26","!#$&+-17C",
  "!#$')-18=C","!#$&).298DC","!#$&).3:9FD","!#$&*+35:GFC","!#$&(,/3;AGF","!#$&(,/4<;HGM","!#$&),/4<<JHE","!#$%)-05=<LJH",
  "!#$%(*058=ELJR","!#$%(+165>@MLK","!##%(+-26?>NMK`","!##%(+.17@?PNMW","!##%'+.17A@JPNOl","!##%'*.28<ADQPMel","!##%'*.288BASQP]nl","!##%'*/398BBTSQUqnl",
  "!!#%'*,359CBNTSOiqnl","!!#%'*,039DCHUTRbsqnl","!!#%'),/3:?DCWUTZusqn","!!#$')-04;:EDXWUSnuspo","!!#%&)-04;;FERXWUgyusv","!!#%&)-05<;GFLZXW`{ywv","!!#$&)+058<HGG[Z^Yt{~#!v","!!#$&(+155<CHH^]^Xn~!~~#!v",
  "!!#$&(+.26=>IKXb^Xh~#)~#!v","!!#$&(,.16>=JKTb^XYz~#!v","!!#$&),.27>?MKKb^XTl~#!v","!!#$&),.27A?MKHb^XT^~#!v","!!#$&(*/29<?GKHX^XTPqv","!!#$&(*/398?AKHP^XTPcv"]

def powers (r : ℕ) : List ℕ :=
  if r=0 then [] else KoalaSplitGateWords.powers (powersTape.getD (r-1) "")

def plainPowers : ℕ → List ℕ
  | _ => []

def tailPowers : List ℕ := KoalaSplitGateWords.powers "!!#$&)+0398?>KHG^YUPUvmdZQH>5,#"

def priced (r:ℕ):Bool:=rowCheck gate r (boxes r) (powers r) (plain r) (plainPowers r)
private theorem priced_list : (List.range 62).all (fun i => priced (i+1)) = true := by decide +kernel

theorem prices {r : ℕ} (hr : 0 < r) (hR : r < terminal) : priced r = true :=
  price hr hR priced_list

theorem tail:plainCheck gate terminal (4012,1650,550) tailPowers=true:=by decide +kernel

private abbrev Chunk (i n v : ℕ) := lossChunk 32 envelope plain boxes i n = v
private theorem checkPart (i n v : ℕ) (ok : Chunk i n v := by decide +kernel) : Chunk i n v := ok
private def part0 := checkPart 0 6 0x2384dc4cc14
private def part1 := checkPart 6 6 0x2384dc4cc14
private def part2 := checkPart 12 6 0x2384dc4cc14
private def part3 := checkPart 18 6 0x2355d9790c7
private def part4 := checkPart 24 6 0x227d4f936d8
private def part5 := checkPart 30 6 0x20f709128dc
private def part6 := checkPart 36 6 0x1e6ec06fb2b
private def part7 := checkPart 42 6 0x1a658a4d41d
private def part8 := checkPart 48 6 0x1444bbadd34
private def part9 := checkPart 54 6 0xd0f125924a
private def part10 := checkPart 60 2 0x2f7be029b3

theorem loss_bound (N : ℕ) : Bound envelope terminal plain boxes 20785659690288 N :=
  loss_of_chunks 32 envelope terminal plain boxes 20785659690288 N (by decide) (by decide)
    (LossSum.empty _ _ _ _
      |>.append 6 0x2384dc4cc14 part0 |>.append 6 0x2384dc4cc14 part1 |>.append 6 0x2384dc4cc14 part2 |>.append 6 0x2355d9790c7 part3
      |>.append 6 0x227d4f936d8 part4 |>.append 6 0x20f709128dc part5 |>.append 6 0x1e6ec06fb2b part6 |>.append 6 0x1a658a4d41d part7
      |>.append 6 0x1444bbadd34 part8 |>.append 6 0xd0f125924a part9 |>.append 2 0x2f7be029b3 part10)

def receipt : KoalaSplitProof.Receipt envelope split unit :=
  ⟨terminal, plain, boxes, powers, plainPowers, tailPowers, 20785659690288,
    by decide,by decide,loss_bound,fun _ h h' => prices h h', tail⟩

end KoalaAt2428Gate51

#print axioms KoalaAt2428Gate51.loss_bound
#print axioms KoalaAt2428Gate51.receipt
