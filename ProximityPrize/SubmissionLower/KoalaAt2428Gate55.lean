import ProximityPrize.SubmissionLower.KoalaGateSharedData
import ProximityPrize.SubmissionLower.KoalaGateChunkSums
import ProximityPrize.SubmissionLower.KoalaSplitGateWords

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000

set_option linter.defProp false

namespace KoalaAt2428Gate55
open KoalaGateSharedData
open FadicGate KoalaGateCheck
open KoalaWeightedRate (Envelope)
open KoalaFarBridge (rowCheck plainCheck)

def envelope : Envelope :=
  ⟨120,54,6,123,54,3120,4423,⟨9104410572,45470044641,9684328784⟩,3531083992272⟩
abbrev split:ℕ:=48
abbrev unit:ℕ:=1919967770880
abbrev terminal:ℕ:=61
abbrev gate:=KoalaSplitRow.rate envelope split unit

private def boxesTape : List (List Entry) := [
  b05n,b04v,b042,b041,b034,b024,b00x,b00z,
  bzw,byp,byq,byr,bxd,bvu,bub,bud,
  bsz,bt1,brz,bs0,bqx,bqw,bps,bpt,
  bou,bng,blq,bk7,bii,bih,bfk,bbd,
  bbj,bbk,bbm,bbo,bbq,bbs,bc2,bc3]
def boxes (r : ℕ) : List FadicGate.Entry :=
  if r < 21 then [] else boxesTape.getD (r-21) []

def plain : ℕ → ℕ × ℕ × ℕ
  | _ => (0,0,0)

private def powersTape : List String := [
  "","","","","","","","",
  "","","","","","","","",
  "","","","","","!#","!#%","!#%",
  "!#%(",z57,"!#%(,0","!#%'-1","!#$'*18","!#$(+298","!#$'+.49","!#$'+.3:",
  "!#$')/3;C","!#$&*/4<<K","!#$&*/4=<LK","!#$&*,58=NL","!#$&)-15>HNL","!#$&)-06?AON","!#$&)-16@?QOV","!#$&).17A@SQO",
  "!#$&(+27<ALSQf","!#$&(+287BFTS]","!#$%(,.48CBVTTu","!#$%(,.29DCXVTl","!##%',/39EDQXVd~#'","!##%(*/3:@EKYXZ{~#'","!##%(*/4;;FE[YXs~#*~#'","!##%(*04;;FF][Yj~#-~#*~#'",
  "!!#%'+-57;GFV][a~#%~#-~#*~#'","!!#%'+-15<HGP_]Zy~#0~#-~#*","!!#%')-05<CHIa_]q~#4~#0~#-~#*","!!#%')-15=>IHba_h~#+~#4~#0~#-~#*","!!#%'*.16>=JI[ba_~#!~#7~#4~#0~#+","!!#%'*.16>>KJUdb`w~#:~#7~#4~#+","!!#$'*,27:>LKNedbn~#1~#:~#6~#+","!!#$'),277?GLKgeb^~#)~#=~#6~#+",
  "!!#%&),/47@BMLafb^u~#@~#6~#+","!!#$&),/28@?NLWfb^e~#/~#6~#+","!!#$&),/38A@NLNfb^X{~#6~#+","!!#$&)-/38A@NLJfb^Xk~#6~#+"]

def powers (r : ℕ) : List ℕ :=
  if r=0 then [] else KoalaSplitGateWords.powers (powersTape.getD (r-1) "")

def plainPowers : ℕ → List ℕ
  | _ => []

def tailPowers : List ℕ := KoalaSplitGateWords.powers "!!#$&(+049=@IMK`ea[b~#-~#4~#)|qg[QF<s"

def priced (r:ℕ):Bool:=rowCheck gate r (boxes r) (powers r) (plain r) (plainPowers r)
private theorem priced_list : (List.range 60).all (fun i => priced (i+1)) = true := by decide +kernel

theorem prices {r : ℕ} (hr : 0 < r) (hR : r < terminal) : priced r = true :=
  price hr hR priced_list

theorem tail:plainCheck gate terminal (4012,1650,550) tailPowers=true:=by decide +kernel

private abbrev Chunk (i n v : ℕ) := lossChunk 32 envelope plain boxes i n = v
private theorem checkPart (i n v : ℕ) (ok : Chunk i n v := by decide +kernel) : Chunk i n v := ok
private def part0 := checkPart 0 6 0x2384dc4cc14
private def part1 := checkPart 6 6 0x2384dc4cc14
private def part2 := checkPart 12 6 0x2384dc4cc14
private def part3 := checkPart 18 6 0x235b368547e
private def part4 := checkPart 24 6 0x228dd685af9
private def part5 := checkPart 30 6 0x211dad78ca0
private def part6 := checkPart 36 6 0x1ea19f666ee
private def part7 := checkPart 42 6 0x1abb3730007
private def part8 := checkPart 48 6 0x14d89a84a6a
private def part9 := checkPart 54 6 0xde29bc6c8e

theorem loss_bound (N : ℕ) : Bound envelope terminal plain boxes 20731098611264 N :=
  loss_of_chunks 32 envelope terminal plain boxes 20731098611264 N (by decide) (by decide)
    (LossSum.empty _ _ _ _
      |>.append 6 0x2384dc4cc14 part0 |>.append 6 0x2384dc4cc14 part1 |>.append 6 0x2384dc4cc14 part2 |>.append 6 0x235b368547e part3
      |>.append 6 0x228dd685af9 part4 |>.append 6 0x211dad78ca0 part5 |>.append 6 0x1ea19f666ee part6 |>.append 6 0x1abb3730007 part7
      |>.append 6 0x14d89a84a6a part8 |>.append 6 0xde29bc6c8e part9)

def receipt : KoalaSplitProof.Receipt envelope split unit :=
  ⟨terminal, plain, boxes, powers, plainPowers, tailPowers, 20731098611264,
    by decide,by decide,loss_bound,fun _ h h' => prices h h', tail⟩

end KoalaAt2428Gate55

#print axioms KoalaAt2428Gate55.loss_bound
#print axioms KoalaAt2428Gate55.receipt
