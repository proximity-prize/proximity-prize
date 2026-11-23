import ProximityPrize.SubmissionLower.KoalaGateSharedData
import ProximityPrize.SubmissionLower.KoalaGateChunkSums
import ProximityPrize.SubmissionLower.KoalaSplitGateWords

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000

set_option linter.defProp false

namespace KoalaAt2428Gate68
open KoalaGateSharedData
open FadicGate KoalaGateCheck
open KoalaWeightedRate (Envelope)
open KoalaFarBridge (rowCheck plainCheck)

def envelope : Envelope :=
  ⟨134,52,3,135,52,3484,4435,⟨3552480427,15113173520,129204591065⟩,1474987061820⟩
abbrev split:ℕ:=48
abbrev unit:ℕ:=1919966568960
abbrev terminal:ℕ:=58
abbrev gate:=KoalaSplitRow.rate envelope split unit

private def boxesTape : List (List Entry) := [
  b05v,b053,b049,b046,b03e,b02c,b013,b014,
  b004,byv,bxh,bxf,bxi,bvz,bug,bt3,
  bs0,bs3,bs4,bqy,br3,bpr,bpy,boo,
  bom,bna,bnb,bn7,blr,b59.take 19,bim,bin,
  bip,bir]
def boxes (r : ℕ) : List FadicGate.Entry :=
  if r < 24 then [] else boxesTape.getD (r-24) []

def plain : ℕ → ℕ × ℕ × ℕ
  | _ => (0,0,0)

private def powersTape : List String := [
  "","","","","","","","",
  "","","","","","","","",
  "","","","","","","","",
  "!#","!#%","!#$","!#$&","!#$')","!#$')/",z5T,"!#$&*,0",
  "!#$&(-06","!#$&)-176","!#$&)-187","!#$&)+238","!#$%(+.29>","!#$%(+.2:8E","!#$&(,.3::GE","!#$%(,/3;:HGE",
  "!##%'*/46;BHG","!##%'*044<<JH","!##%'*,04=<KJH","!##%(*-05==LKJ","!##%'+-06>=FLKH","!##%')-169>@MLI","!##%')-176?>OMLU","!##%').177@?POMM",
  "!!#$&)+237A@JPOLb","!!#%&*+.28AADQPNY","!!#%&(,.28=A@RQPR","!!#$'(,/298BATRQNg","!!#$&),/399CBMTRQ_q",z6R,"!!#$&)*/46:EDCWVXPls",z6Q,
  "!!#$&(+-04;;FHS]XT_}"]

def powers (r : ℕ) : List ℕ :=
  if r=0 then [] else KoalaSplitGateWords.powers (powersTape.getD (r-1) "")

def plainPowers : ℕ → List ℕ
  | _ => []

def tailPowers : List ℕ := KoalaSplitGateWords.powers "!!#$')-/27?>KIQ_[WWy~#!wog_VNFLy"

def priced (r:ℕ):Bool:=rowCheck gate r (boxes r) (powers r) (plain r) (plainPowers r)
private theorem priced_list : (List.range 57).all (fun i => priced (i+1)) = true := by decide +kernel

theorem prices {r : ℕ} (hr : 0 < r) (hR : r < terminal) : priced r = true :=
  price hr hR priced_list

theorem tail:plainCheck gate terminal (4012,1650,550) tailPowers=true:=by decide +kernel

private abbrev Chunk (i n v : ℕ) := lossChunk 96 envelope plain boxes i n = v
private theorem checkPart (i n v : ℕ) (ok : Chunk i n v := by decide +kernel) : Chunk i n v := ok
private def part0 := checkPart 0 6 0x2384dc4cc14
private def part1 := checkPart 6 6 0x2384dc4cc14
private def part2 := checkPart 12 6 0x2384dc4cc14
private def part3 := checkPart 18 6 0x237fcffb077
private def part4 := checkPart 24 6 0x22e77affa8d
private def part5 := checkPart 30 6 0x21a00518ea2
private def part6 := checkPart 36 6 0x1f773c82af0
private def part7 := checkPart 42 6 0x1c305106096
private def part8 := checkPart 48 6 0x17599485a0d
private def part9 := checkPart 54 3 0x96be167dd6

theorem loss_bound (N : ℕ) : Bound envelope terminal plain boxes 20822782050635 N :=
  loss_of_chunks 96 envelope terminal plain boxes 20822782050635 N (by decide) (by decide)
    (LossSum.empty _ _ _ _
      |>.append 6 0x2384dc4cc14 part0 |>.append 6 0x2384dc4cc14 part1 |>.append 6 0x2384dc4cc14 part2 |>.append 6 0x237fcffb077 part3
      |>.append 6 0x22e77affa8d part4 |>.append 6 0x21a00518ea2 part5 |>.append 6 0x1f773c82af0 part6 |>.append 6 0x1c305106096 part7
      |>.append 6 0x17599485a0d part8 |>.append 3 0x96be167dd6 part9)

def receipt : KoalaSplitProof.Receipt envelope split unit :=
  ⟨terminal, plain, boxes, powers, plainPowers, tailPowers, 20822782050635,
    by decide,by decide,loss_bound,fun _ h h' => prices h h', tail⟩

end KoalaAt2428Gate68

#print axioms KoalaAt2428Gate68.loss_bound
#print axioms KoalaAt2428Gate68.receipt
