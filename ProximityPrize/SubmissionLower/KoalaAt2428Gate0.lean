import ProximityPrize.SubmissionLower.KoalaGateSharedData
import ProximityPrize.SubmissionLower.KoalaGateChunkSums
import ProximityPrize.SubmissionLower.KoalaSplitGateWords

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000

set_option linter.defProp false

namespace KoalaAt2428Gate0
open KoalaGateSharedData
open FadicGate KoalaGateCheck
open KoalaWeightedRate (Envelope)
open KoalaFarBridge (rowCheck plainCheck)

def envelope : Envelope :=
  ⟨106,54,10,112,55,2756,4262,⟨9630419928,40855342412,9021710858⟩,3300237690289⟩
abbrev split:ℕ:=24
abbrev unit:ℕ:=1920000000000
abbrev terminal:ℕ:=59
abbrev gate:=KoalaSplitRow.rate envelope split unit

private def boxesTape : List (List Entry) := [
  b05r,b051,b045,b039,b026,b028,b012,b003,
  byq,byr,bxd,bxh,bt0.take 10,bud,bsz,bt1,
  bt3,bs0,bs3,bqw,bqy,bpt,bpr,bok,
  boo,bfm.take 17,bfj.take 18,bbb.take 19,bik,bfo,bfn,bfp,
  bfq,bfr,bfs,bft]
def boxes (r : ℕ) : List FadicGate.Entry :=
  if r < 23 then [] else boxesTape.getD (r-23) []

def plain : ℕ → ℕ × ℕ × ℕ
  | _ => (0,0,0)

private def powersTape : List String := [
  "","","","","","","","",
  "","","","","","","","",
  "","","","","","","","!#",
  "!!$","!!$'","!!$'+","!!$&+","!!$&)/","!!$&)/6","!!#%),16","!!#&),07",
  "!!#&(,08>","!!#%(-187","!!#%(-198G","!!#%(*249HG","!!#%'*.2:BHG","!!#%'+.2;;JH","!!#%'+.3<;KJ","!!#$'+.3<<MKI",
  "!!#$&)/47<FMK","!!#$&)/54=@NMQ","!!#$'),05>=ONL","!!#$'*,/5?>QON`","!!#$&*,06@?JQOV","!!#$&(,06:@DRQNo","!!#$&(-076@@TRQf","!!#$&(-177A@UTR]}",
  "!!!$%(*137BANUTSt}","!!!$%)*.18CBHVUSk~##}","!!!$%'+-28>CBXVUc~#&~##}","!!!#%'+.299DCYXVXz~#&~##}","!!!#%'+.299EDSYXUq~#)~#&~##","!!!#%(+.3:9EDL[YWh~#+~#)~#&","!!!#%().35:FEE]ZY^~#!~#+~#'","!!!#%')/33:AFE^]YUv~#.~#'",
  "!!!#%'),03;<GFV^YUf~#1~#'","!!!#%'*,/4;;HFN^YUU}~#'"]
def powers (r : ℕ) : List ℕ :=
  if r=0 then [] else KoalaSplitGateWords.powers (powersTape.getD (r-1) "")

def plainPowers : ℕ → List ℕ
  | _ => []

def tailPowers:List ℕ:=KoalaSplitGateWords.powers "!!!#%'*-05=<JHIb_ZW|~#6~#.~#%yph_U~#Q~%6~%K"

def priced (r:ℕ):Bool:=rowCheck gate r (boxes r) (powers r) (plain r) (plainPowers r)
private theorem priced_list : (List.range 58).all (fun i => priced (i+1)) = true := by decide +kernel

theorem prices {r : ℕ} (hr : 0 < r) (hR : r < terminal) : priced r = true :=
  price hr hR priced_list

theorem tail:plainCheck gate terminal (4012,1650,550) tailPowers=true:=by decide +kernel

private abbrev Chunk (i n v : ℕ) := lossChunk 64 envelope plain boxes i n = v
private theorem checkPart (i n v : ℕ) (ok : Chunk i n v := by decide +kernel) : Chunk i n v := ok
private def part0 := checkPart 0 6 0x2384dc4cc14
private def part1 := checkPart 6 6 0x2384dc4cc14
private def part2 := checkPart 12 6 0x2384dc4cc14
private def part3 := checkPart 18 6 0x2376315b1f0
private def part4 := checkPart 24 6 0x22be2d647f2
private def part5 := checkPart 30 6 0x21654ba713d
private def part6 := checkPart 36 6 0x1f2c07c779d
private def part7 := checkPart 42 6 0x1bbef923ad5
private def part8 := checkPart 48 6 0x167a637af2b
private def part9 := checkPart 54 4 0xb767112c96

theorem loss_bound (N : ℕ) : Bound envelope terminal plain boxes 20823096974734 N :=
  loss_of_chunks 64 envelope terminal plain boxes 20823096974734 N (by decide) (by decide)
    (LossSum.empty _ _ _ _
      |>.append 6 0x2384dc4cc14 part0 |>.append 6 0x2384dc4cc14 part1 |>.append 6 0x2384dc4cc14 part2 |>.append 6 0x2376315b1f0 part3
      |>.append 6 0x22be2d647f2 part4 |>.append 6 0x21654ba713d part5 |>.append 6 0x1f2c07c779d part6 |>.append 6 0x1bbef923ad5 part7
      |>.append 6 0x167a637af2b part8 |>.append 4 0xb767112c96 part9)

def receipt : KoalaSplitProof.Receipt envelope split unit :=
  ⟨terminal, plain, boxes, powers, plainPowers, tailPowers, 20823096974734,
    by decide,by decide,loss_bound,fun _ h h' => prices h h', tail⟩

end KoalaAt2428Gate0

#print axioms KoalaAt2428Gate0.loss_bound
#print axioms KoalaAt2428Gate0.receipt
