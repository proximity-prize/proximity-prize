import ProximityPrize.SubmissionLower.KoalaGateSharedData
import ProximityPrize.SubmissionLower.KoalaGateChunkSums
import ProximityPrize.SubmissionLower.KoalaSplitGateWords

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000

set_option linter.defProp false

namespace KoalaAt2428Gate72
open KoalaGateSharedData
open FadicGate KoalaGateCheck
open KoalaWeightedRate (Envelope)
open KoalaFarBridge (rowCheck plainCheck)

def envelope : Envelope :=
  ⟨135,46,11,135,46,3510,4435,⟨6294861209,44272165085,7502467200⟩,2823242839841⟩
abbrev split:ℕ:=48
abbrev unit:ℕ:=1919968594560
abbrev terminal:ℕ:=59
abbrev gate:=KoalaSplitRow.rate envelope split unit

private def boxesTape : List (List Entry) := [
  b05m,b04w,b041,b034,b024,b00x,b00z,bzw,
  byp,byq,byr,bxd,bvu,bub,bud,bsz,
  bt1,brz,bs0,bqx,bqw,bps,bpt,bpr,
  bok,bn6,blm,bk4,bih,bfk,bbx,bc6,
  bc8,bby,bbz,bc0,bc1]
def boxes (r : ℕ) : List FadicGate.Entry :=
  if r < 22 then [] else boxesTape.getD (r-22) []

def plain : ℕ → ℕ × ℕ × ℕ
  | _ => (0,0,0)

private def powersTape : List String := [
  "","","","","","","","",
  "","","","","","","","",
  "","","","","","","!#","!#%",
  "!#$'",z3p,"!#$'+.","!#$'+/","!#$')/5",z5j,z4Q,"!#$&*-07",
  z6W,"!#$&)-187D","!#$&).298FD","!#$&)+249GF","!#$%(+.2:AGF","!#$&(+.3;:HG","!#$&(,/4<;JHF","!#$%(,/4<<KJH",
  "!##%'*057<EKJT","!##%'*055=>LKK","!##%(*-15>=NLJc","!##%(+-06?>ONLY","!##%'+-16@?IONP","!##%')-17;@BQOLh","!##%').177@@RQO_t","!##%').287A@SRQUvt",
  "!!#%&*+248BAMSROmvt","!!#%&*,/28CBFUSRdyvt","!!#%'(,/39>CBVUSZ{yvt","!!#$'),/399DCWVUQs{yvs","!!#$&),/3:9EDQWVTi~!~{xs","!!#$&),/4::EEJYXVa~##~!~{s","!!#$&)*046:FEDZYWWw~##|s","!!#$&(+044;AFF]ZWSn~#&|s",
  "!!#$&(+-14<<GFU[WS_~#(|s","!!#$&(+-05<<HFM[WSPu|s"]

def powers (r : ℕ) : List ℕ :=
  if r=0 then [] else KoalaSplitGateWords.powers (powersTape.getD (r-1) "")

def plainPowers : ℕ → List ℕ
  | _ => []

def tailPowers : List ℕ := KoalaSplitGateWords.powers "!!#$&),.27?>KIJc`[X{~#5~#-~#%{skc[~#j~%'"

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
private def part3 := checkPart 18 6 0x236a2e16955
private def part4 := checkPart 24 6 0x22a8c2e1ff8
private def part5 := checkPart 30 6 0x21616ad8284
private def part6 := checkPart 36 6 0x1f2c68eaa21
private def part7 := checkPart 42 6 0x1bc46cb55aa
private def part8 := checkPart 48 6 0x168267cf2d4
private def part9 := checkPart 54 4 0xb8ad92e101

theorem loss_bound (N : ℕ) : Bound envelope terminal plain boxes 20822277571501 N :=
  loss_of_chunks 48 envelope terminal plain boxes 20822277571501 N (by decide) (by decide)
    (LossSum.empty _ _ _ _
      |>.append 6 0x2384dc4cc14 part0 |>.append 6 0x2384dc4cc14 part1 |>.append 6 0x2384dc4cc14 part2 |>.append 6 0x236a2e16955 part3
      |>.append 6 0x22a8c2e1ff8 part4 |>.append 6 0x21616ad8284 part5 |>.append 6 0x1f2c68eaa21 part6 |>.append 6 0x1bc46cb55aa part7
      |>.append 6 0x168267cf2d4 part8 |>.append 4 0xb8ad92e101 part9)

def receipt : KoalaSplitProof.Receipt envelope split unit :=
  ⟨terminal, plain, boxes, powers, plainPowers, tailPowers, 20822277571501,
    by decide,by decide,loss_bound,fun _ h h' => prices h h', tail⟩

end KoalaAt2428Gate72

#print axioms KoalaAt2428Gate72.loss_bound
#print axioms KoalaAt2428Gate72.receipt
