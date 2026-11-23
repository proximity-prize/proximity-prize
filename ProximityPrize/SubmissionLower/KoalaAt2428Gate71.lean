import ProximityPrize.SubmissionLower.KoalaGateSharedData
import ProximityPrize.SubmissionLower.KoalaGateChunkSums
import ProximityPrize.SubmissionLower.KoalaSplitGateWords

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000

set_option linter.defProp false

namespace KoalaAt2428Gate71
open KoalaGateSharedData
open FadicGate KoalaGateCheck
open KoalaWeightedRate (Envelope)
open KoalaFarBridge (rowCheck plainCheck)

def envelope : Envelope :=
  ⟨136,46,10,136,46,3536,4436,⟨6292754254,45603595121,4961110289⟩,2848884595766⟩
abbrev split:ℕ:=48
abbrev unit:ℕ:=1919968421760
abbrev terminal:ℕ:=59
abbrev gate:=KoalaSplitRow.rate envelope split unit

private def boxesTape : List (List Entry) := [
  b05m,b04w,b041,b034,b024,b026,b00z,bzw,
  byp,byq,byr,bxd,bvu,bub,bud,bsz,
  bt1,brz,bs0,bqx,bqw,bps,bpt,bpr,
  bok,bn6,blm,bk4,bih,bfk,bfv,b7f.take 22,
  b7w.take 22,b86.take 22,b8l.take 22,b8s.take 22,b96.take 22]
def boxes (r : ℕ) : List FadicGate.Entry :=
  if r < 22 then [] else boxesTape.getD (r-22) []

def plain : ℕ → ℕ × ℕ × ℕ
  | _ => (0,0,0)

private def powersTape : List String := [
  "","","","","","","","",
  "","","","","","","","",
  "","","","","","","!#","!#%",
  "!#$'",z3p,"!#$(+",z4C,"!#$')/5",z5j,z4Q,"!#$&*-07",
  z6W,"!#$&)-298E","!#$&).299FE","!#$&)+349HF","!#$%(+.3:AHF","!#$&(,/3;:IH","!#$&(,/4<;JIF","!#$%(,/4=<LJI",
  "!##%'*058=ELJU","!##%'*055>?MLL","!##%(*-15>>NMKd","!##%(+-06?>PNMZ","!##%'+-16@?IPNQ","!##%')-17;@CQPMi","!##%').277A@SQP`u","!##%').287BATSQVwu",
  "!!#%&*+248BBMTSOnwu","!!#%&*,/29CBGUTRezwu","!!#%'(,/39>CBWUT]|zwu","!!#$'),/3:9DCXWURt|zv","!!#$&),/3::EDRXWTk~#!|yt","!!#$&)-/4;:FEKYXWb~#%~!~|t","!!#$&)*046;GFE[ZWXx~#$}t","!!#$&(+054;AGF][WTo~#'}t",
  "!!#$&(+-15<<HFV[WT`~#)}t","!!#$&(+-05<<HFM[WTPv}t"]

def powers (r : ℕ) : List ℕ :=
  if r=0 then [] else KoalaSplitGateWords.powers (powersTape.getD (r-1) "")

def plainPowers : ℕ → List ℕ
  | _ => []

def tailPowers : List ℕ := KoalaSplitGateWords.powers "!!#$&),/27?>LJKc`]X|~#6~#.~#&{skc]~#r~%1"

def priced (r:ℕ):Bool:=rowCheck gate r (boxes r) (powers r) (plain r) (plainPowers r)
private theorem priced_list : (List.range 58).all (fun i => priced (i+1)) = true := by decide +kernel

theorem prices {r : ℕ} (hr : 0 < r) (hR : r < terminal) : priced r = true :=
  price hr hR priced_list

theorem tail:plainCheck gate terminal (4012,1650,550) tailPowers=true:=by decide +kernel

private abbrev Chunk (i n v : ℕ) := lossChunk 48 envelope plain boxes i n = v
private theorem checkPart (i n v : ℕ) (ok : Chunk i n v := by decide +kernel) : Chunk i n v := ok
private def part0 := checkPart 0 6 0x2384dc4cc14
private def part1 := checkPart 6 6 0x2384dc4cc14
private def part2 := checkPart 12 6 0x2384dc4cc14
private def part3 := checkPart 18 6 0x236a2275e81
private def part4 := checkPart 24 6 0x22abf39b679
private def part5 := checkPart 30 6 0x21606b4cd11
private def part6 := checkPart 36 6 0x1f2a57425a3
private def part7 := checkPart 42 6 0x1bc0a6856c1
private def part8 := checkPart 48 6 0x167fce02dc1
private def part9 := checkPart 54 4 0xb8562b6783

theorem loss_bound (N : ℕ) : Bound envelope terminal plain boxes 20819120773103 N :=
  loss_of_chunks 48 envelope terminal plain boxes 20819120773103 N (by decide) (by decide)
    (LossSum.empty _ _ _ _
      |>.append 6 0x2384dc4cc14 part0 |>.append 6 0x2384dc4cc14 part1 |>.append 6 0x2384dc4cc14 part2 |>.append 6 0x236a2275e81 part3
      |>.append 6 0x22abf39b679 part4 |>.append 6 0x21606b4cd11 part5 |>.append 6 0x1f2a57425a3 part6 |>.append 6 0x1bc0a6856c1 part7
      |>.append 6 0x167fce02dc1 part8 |>.append 4 0xb8562b6783 part9)

def receipt : KoalaSplitProof.Receipt envelope split unit :=
  ⟨terminal, plain, boxes, powers, plainPowers, tailPowers, 20819120773103,
    by decide,by decide,loss_bound,fun _ h h' => prices h h', tail⟩

end KoalaAt2428Gate71

#print axioms KoalaAt2428Gate71.loss_bound
#print axioms KoalaAt2428Gate71.receipt
