import ProximityPrize.SubmissionLower.KoalaGateSharedData
import ProximityPrize.SubmissionLower.KoalaGateChunkSums
import ProximityPrize.SubmissionLower.KoalaSplitGateWords

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000

set_option linter.defProp false

namespace KoalaAt2428Gate59
open KoalaGateSharedData
open FadicGate KoalaGateCheck
open KoalaWeightedRate (Envelope)
open KoalaFarBridge (rowCheck plainCheck)

def envelope : Envelope :=
  ⟨132,51,2,135,51,3432,4435,⟨3541268738,15416655455,128188974115⟩,1469330465100⟩
abbrev split:ℕ:=48
abbrev unit:ℕ:=1919966551680
abbrev terminal:ℕ:=58
abbrev gate:=KoalaSplitRow.rate envelope split unit

private def boxesTape : List (List Entry) := [
  b05v,b053,b049,b03a,b03e,b02c,b013,b000,
  b004,byv,bxh,bxf,bxi,bvz,bug,bt3,
  bs0,bs3,bqw,bqy,br3,bpr,bpy,boo,
  bom,bna,bnb,bbc.take 18,b5o.take 19,b59.take 20,bim,bin,
  bip,bir]
def boxes (r : ℕ) : List FadicGate.Entry :=
  if r < 24 then [] else boxesTape.getD (r-24) []

def plain : ℕ → ℕ × ℕ × ℕ
  | _ => (0,0,0)

private def powersTape : List String := [
  "","","","","","","","",
  "","","","","","","","",
  "","","","","","","","",
  "!#","!#%","!#$'","!#$&","!#$')","!#$')/","!#$&*,0","!#$&*,0",
  "!#$&(-06","!#$&)-176","!#$&)-187","!#$&)+238","!#$%(+.29>","!#$%(+.2:8E","!#$&(,.3::GE","!#$%(,/3;:HGE",
  "!##%'*/46;BHG","!##%'*044<<IHE","!##%'*,04=<KIG","!##%(*-05==LKI","!##%'+-06>=FLKH","!##%')-169>@MLI","!##%')-176?>OMLU","!##%').177@?POMM",
  "!!#$&)+237A@JPOKb","!!#%&*+.28AACQPNY","!!#%&(,.28=A@RQPRn","!!#$'(,/298BATRQNgn","!!#$&),/399CBMTRP_qn",z6R,"!!#$&)*/46:EDCWVXPks",z6Q,
  "!!#$&(+-04;;FGS]XT_}"]

def powers (r : ℕ) : List ℕ :=
  if r=0 then [] else KoalaSplitGateWords.powers (powersTape.getD (r-1) "")

def plainPowers : ℕ → List ℕ
  | _ => []

def tailPowers : List ℕ := KoalaSplitGateWords.powers "!!#$')-/27?>KIR`]XZ|~#%zrjcZRJ`~#.l"

def priced (r:ℕ):Bool:=rowCheck gate r (boxes r) (powers r) (plain r) (plainPowers r)
private theorem priced_list : (List.range 57).all (fun i => priced (i+1)) = true := by decide +kernel

theorem prices {r : ℕ} (hr : 0 < r) (hR : r < terminal) : priced r = true :=
  price hr hR priced_list

theorem tail:plainCheck gate terminal (4012,1650,550) tailPowers=true:=by decide +kernel

private abbrev Chunk (i n v : ℕ) := lossChunk 64 envelope plain boxes i n = v
private theorem checkPart (i n v : ℕ) (ok : Chunk i n v := by decide +kernel) : Chunk i n v := ok
private def part0 := checkPart 0 6 0x2384dc4cc14
private def part1 := checkPart 6 6 0x2384dc4cc14
private def part2 := checkPart 12 6 0x2384dc4cc14
private def part3 := checkPart 18 6 0x237f769925e
private def part4 := checkPart 24 6 0x22d7525623e
private def part5 := checkPart 30 6 0x21795f3a839
private def part6 := checkPart 36 6 0x1f2b10c7efa
private def part7 := checkPart 42 6 0x1bb0fdd3be1
private def part8 := checkPart 48 6 0x1675cb2978c
private def part9 := checkPart 54 3 0x8d200a6216

theorem loss_bound (N : ℕ) : Bound envelope terminal plain boxes 20650898470286 N :=
  loss_of_chunks 64 envelope terminal plain boxes 20650898470286 N (by decide) (by decide)
    (LossSum.empty _ _ _ _
      |>.append 6 0x2384dc4cc14 part0 |>.append 6 0x2384dc4cc14 part1 |>.append 6 0x2384dc4cc14 part2 |>.append 6 0x237f769925e part3
      |>.append 6 0x22d7525623e part4 |>.append 6 0x21795f3a839 part5 |>.append 6 0x1f2b10c7efa part6 |>.append 6 0x1bb0fdd3be1 part7
      |>.append 6 0x1675cb2978c part8 |>.append 3 0x8d200a6216 part9)

def receipt : KoalaSplitProof.Receipt envelope split unit :=
  ⟨terminal, plain, boxes, powers, plainPowers, tailPowers, 20650898470286,
    by decide,by decide,loss_bound,fun _ h h' => prices h h', tail⟩

end KoalaAt2428Gate59

#print axioms KoalaAt2428Gate59.loss_bound
#print axioms KoalaAt2428Gate59.receipt
