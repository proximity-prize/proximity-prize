import ProximityPrize.SubmissionLower.KoalaGateSharedData
import ProximityPrize.SubmissionLower.KoalaGateChunkSums
import ProximityPrize.SubmissionLower.KoalaSplitGateWords

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000

set_option linter.defProp false

namespace KoalaAt2428Gate65
open KoalaGateSharedData
open FadicGate KoalaGateCheck
open KoalaWeightedRate (Envelope)
open KoalaFarBridge (rowCheck plainCheck)

def envelope : Envelope :=
  ⟨128,47,8,131,47,3328,4431,⟨6797742764,44986096707,6723225327⟩,2907405298809⟩
abbrev split:ℕ:=48
abbrev unit:ℕ:=1919968032000
abbrev terminal:ℕ:=59
abbrev gate:=KoalaSplitRow.rate envelope split unit

private def boxesTape : List (List Entry) := [
  b04v,b042,b041,b034,b024,b00x,b00z,bzw,
  byp,byq,byr,bxd,bvu,bub,bud,bsz,
  bt1,brz,bs0,bqx,bqw,bps,bpt,bpr,
  bok,bn6,blm,bk4,bih,bfk,bbd,bbj,
  bbk,bbm,bbo,bbq,bbs]
def boxes (r : ℕ) : List FadicGate.Entry :=
  if r < 22 then [] else boxesTape.getD (r-22) []

def plain : ℕ → ℕ × ℕ × ℕ
  | _ => (0,0,0)

private def powersTape : List String := [
  "","","","","","","","",
  "","","","","","","","",
  "","","","","","!#","!#%","!#%",
  "!#%'",z3p,"!#$(+/",z4C,z65,"!#$'*076","!#$&*,17","!#$&*-17",
  "!#$&)-18>","!#$&).298F","!#$&).2:9GF","!#$&)+35:HG","!#$&(+/3;BHG","!#$&(,/3<;JH","!#$&(,/4<<KJH","!#$%(,05=<MKI",
  "!##%'*058=FMKW","!#$%(*065>@NMN","!##%(+-16?>ONLf","!##%(+-16@?QON]","!##%'+-17A@JQOS","!##%').17;ADRQNk","!##%').287AATRQbw","!##%'*.288BAUTRXyw",
  "!!#%&*,348CBNUTPpyw","!!#%'*,/39DCHVUSh|yw","!!#%'),/3:?DCXVU_~#!|yw","!!#$'),/3::EDYXVUv~#!|yw","!!#$&)-/4;:FESYXUm~#$~#!|w","!!#$&)-04;;FFL[YXd~#'~#$~#!w","!!#$&)+057;GGF][Y[{~#'~##w","!!#$&(+055<BGG_]YUs~#*~##w",
  "!!#$&(+-15<=HGW^YUc~#-~##w","!!#$&(+-15=<IGO^YUSz~##w"]

def powers (r : ℕ) : List ℕ :=
  if r=0 then [] else KoalaSplitGateWords.powers (powersTape.getD (r-1) "")

def plainPowers : ℕ → List ℕ
  | _ => []

def tailPowers : List ℕ := KoalaSplitGateWords.powers "!!#$&),/27@>LKLea^Y~!~~#9~#1~#)}ume]~#k~%#~%A~$b"

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
private def part3 := checkPart 18 6 0x2363514fb91
private def part4 := checkPart 24 6 0x22a98f09fe6
private def part5 := checkPart 30 6 0x216367949aa
private def part6 := checkPart 36 6 0x1f307e59f45
private def part7 := checkPart 42 6 0x1bcb8ccb552
private def part8 := checkPart 48 6 0x168e7d6e994
private def part9 := checkPart 54 4 0xb964c9c716

theorem loss_bound (N : ℕ) : Bound envelope terminal plain boxes 20830509616798 N :=
  loss_of_chunks 48 envelope terminal plain boxes 20830509616798 N (by decide) (by decide)
    (LossSum.empty _ _ _ _
      |>.append 6 0x2384dc4cc14 part0 |>.append 6 0x2384dc4cc14 part1 |>.append 6 0x2384dc4cc14 part2 |>.append 6 0x2363514fb91 part3
      |>.append 6 0x22a98f09fe6 part4 |>.append 6 0x216367949aa part5 |>.append 6 0x1f307e59f45 part6 |>.append 6 0x1bcb8ccb552 part7
      |>.append 6 0x168e7d6e994 part8 |>.append 4 0xb964c9c716 part9)

def receipt : KoalaSplitProof.Receipt envelope split unit :=
  ⟨terminal, plain, boxes, powers, plainPowers, tailPowers, 20830509616798,
    by decide,by decide,loss_bound,fun _ h h' => prices h h', tail⟩

end KoalaAt2428Gate65

#print axioms KoalaAt2428Gate65.loss_bound
#print axioms KoalaAt2428Gate65.receipt
