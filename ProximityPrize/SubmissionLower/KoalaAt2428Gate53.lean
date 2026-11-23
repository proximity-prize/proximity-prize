import ProximityPrize.SubmissionLower.KoalaGateSharedData
import ProximityPrize.SubmissionLower.KoalaGateChunkSums
import ProximityPrize.SubmissionLower.KoalaSplitGateWords

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000

set_option linter.defProp false

namespace KoalaAt2428Gate53
open KoalaGateSharedData
open FadicGate KoalaGateCheck
open KoalaWeightedRate (Envelope)
open KoalaFarBridge (rowCheck plainCheck)

def envelope : Envelope :=
  ⟨115,56,6,115,56,2990,4390,⟨10140788502,43260254294,11013696930⟩,3576800733743⟩
abbrev split:ℕ:=48
abbrev unit:ℕ:=1919968187520
abbrev terminal:ℕ:=62
abbrev gate:=KoalaSplitRow.rate envelope split unit

private def boxesTape : List (List Entry) := [
  b05n,b04v,b042,b036,b025,b024,b00x,bzy,
  bzw,byp,byq,bxe,bvw,bua,bub,bsy,
  bsz,bs1,brz,bs0,bqx,bqw,bps,bpt,
  bou,blo,bk6,bifAtom,bii,bfl,bfk,bbi,
  bbg,bbh,bbl,bbn,bbp,bbr,bbt,bbu,
  bbw]
def boxes (r : ℕ) : List FadicGate.Entry :=
  if r < 21 then [] else boxesTape.getD (r-21) []

def plain : ℕ → ℕ × ℕ × ℕ
  | _ => (0,0,0)

private def powersTape : List String := [
  "","","","","","","","",
  "","","","","","","","",
  "","","","","","!#","!#%","!#%)",
  z57,z57,"!#%(-0",z4H,"!#$'*29","!#$(+2:9","!#$'+.5:","!#$'+.3;J",
  "!#$'*/3;CJ","!#$&*/4<=KJ",z62,"!#$'*,58=OMQ","!#$&)-15>HOM","!#$&)-06?BPOa","!#$&)-17@?RPW","!#$&).17A@TRP",
  "!#$&(+28<AMTRg","!#$&(+288BGUT_","!#$%(,/48CBWUUw","!#$%),/39DCXWUn","!##%',/3:EDRXWe~#)",z6C,z5o,z5G,
  z5F,z4z,z4y,z4e,z4f,z4s,z4q,z4r,
  z5E,z5D,z5a,z5b,z5Z]

def powers (r : ℕ) : List ℕ :=
  if r=0 then [] else KoalaSplitGateWords.powers (powersTape.getD (r-1) "")

def plainPowers : ℕ → List ℕ
  | _ => []

def tailPowers : List ℕ := KoalaSplitGateWords.powers "!!#$&)+0498ACNKVea[Wy~#4~#){pfZOD9"

def priced (r:ℕ):Bool:=rowCheck gate r (boxes r) (powers r) (plain r) (plainPowers r)
private theorem priced_list : (List.range 61).all (fun i => priced (i+1)) = true := by decide +kernel

theorem prices {r : ℕ} (hr : 0 < r) (hR : r < terminal) : priced r = true :=
  price hr hR priced_list

theorem tail:plainCheck gate terminal (4012,1650,550) tailPowers=true:=by decide +kernel

private abbrev Chunk (i n v : ℕ) := lossChunk 32 envelope plain boxes i n = v
private theorem checkPart (i n v : ℕ) (ok : Chunk i n v := by decide +kernel) : Chunk i n v := ok
private def part0 := checkPart 0 6 0x2384dc4cc14
private def part1 := checkPart 6 6 0x2384dc4cc14
private def part2 := checkPart 12 6 0x2384dc4cc14
private def part3 := checkPart 18 6 0x2356c30c081
private def part4 := checkPart 24 6 0x22829a191d8
private def part5 := checkPart 30 6 0x21046ea5cc1
private def part6 := checkPart 36 6 0x1e89de4f6f9
private def part7 := checkPart 42 6 0x1a8bf022328
private def part8 := checkPart 48 6 0x1497aefd29f
private def part9 := checkPart 54 6 0xda1c01d8b6
private def part10 := checkPart 60 1 0x1ae7829815

theorem loss_bound (N : ℕ) : Bound envelope terminal plain boxes 20781759623393 N :=
  loss_of_chunks 32 envelope terminal plain boxes 20781759623393 N (by decide) (by decide)
    (LossSum.empty _ _ _ _
      |>.append 6 0x2384dc4cc14 part0 |>.append 6 0x2384dc4cc14 part1 |>.append 6 0x2384dc4cc14 part2 |>.append 6 0x2356c30c081 part3
      |>.append 6 0x22829a191d8 part4 |>.append 6 0x21046ea5cc1 part5 |>.append 6 0x1e89de4f6f9 part6 |>.append 6 0x1a8bf022328 part7
      |>.append 6 0x1497aefd29f part8 |>.append 6 0xda1c01d8b6 part9 |>.append 1 0x1ae7829815 part10)

def receipt : KoalaSplitProof.Receipt envelope split unit :=
  ⟨terminal, plain, boxes, powers, plainPowers, tailPowers, 20781759623393,
    by decide,by decide,loss_bound,fun _ h h' => prices h h', tail⟩

end KoalaAt2428Gate53

#print axioms KoalaAt2428Gate53.loss_bound
#print axioms KoalaAt2428Gate53.receipt
