import ProximityPrize.SubmissionLower.KoalaGateSharedData
import ProximityPrize.SubmissionLower.KoalaGateChunkSums
import ProximityPrize.SubmissionLower.KoalaSplitGateWords

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000

set_option linter.defProp false

namespace KoalaAt2428Gate8
open KoalaGateSharedData
open FadicGate KoalaGateCheck
open KoalaWeightedRate (Envelope)
open KoalaFarBridge (rowCheck plainCheck)

def envelope : Envelope :=
  ⟨116,54,8,119,54,3016,4369,⟨9086170391,43359566846,9147448495⟩,3380747592046⟩
abbrev split:ℕ:=48
abbrev unit:ℕ:=1920000000000
abbrev terminal:ℕ:=59
abbrev gate:=KoalaSplitRow.rate envelope split unit

private def boxesTape : List (List Entry) := [
  b05r,b051,b045,b039,b03a,b028,b012,b013,
  b000,byr,byv,bxh,bxf,bud,bsz,bt1,
  bt3,bs0,bs3,bqw,bqy,bpt,bpr,bok,
  boo,bom,bna,blt,bk8,bil,bfn,bfp,
  bfq,bfr,bfs,bft]
def boxes (r : ℕ) : List FadicGate.Entry :=
  if r < 23 then [] else boxesTape.getD (r-23) []

def plain : ℕ → ℕ × ℕ × ℕ
  | _ => (0,0,0)

private def powersTape : List String := [
  "","","","","","","","",
  "","","","","","","","",
  "","","","","","","","!#",
  "!#%","!#%(","!#$(","!#%',",z5V,z5V,"!#$'+-3","!#$'+.29",
  "!#$').3:","!#$&)/3;;","!#$&*/4<;","!#$&*,47<LK","!#$&(,04=FLK","!#$&)-05>?NL","!#$&)-06?>ON","!#$%)-16@?QOM",
  "!#$&(+17;@JQO","!#$&(+177ADRQX","!##%(+.37BATRP","!#$%(,.28BBUTRh","!##%',.29CBOUT_","!##%'*/39>CIWUUv","!##%'*/3:9DCYWUn","!##%(*/4::EDZYWe",
  z6g,z6S,z5y,z5c,z5L,z5M,z5K,z5J,
  z5n,z5m]
def powers (r : ℕ) : List ℕ :=
  if r=0 then [] else KoalaSplitGateWords.powers (powersTape.getD (r-1) "")

def plainPowers : ℕ → List ℕ
  | _ => []

def tailPowers:List ℕ:=KoalaSplitGateWords.powers "!!#%'*-038A@NLNgc_Z~##~#;~#1~#'zpf[Qj~$p~%#"

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
private def part3 := checkPart 18 6 0x2375e0fb70e
private def part4 := checkPart 24 6 0x22c2912582d
private def part5 := checkPart 30 6 0x21665a1b3d7
private def part6 := checkPart 36 6 0x1f12b6599e5
private def part7 := checkPart 42 6 0x1b958077b02
private def part8 := checkPart 48 6 0x163edc96041
private def part9 := checkPart 54 4 0xb35e6f7a91

theorem loss_bound (N : ℕ) : Bound envelope terminal plain boxes 20773242148615 N :=
  loss_of_chunks 64 envelope terminal plain boxes 20773242148615 N (by decide) (by decide)
    (LossSum.empty _ _ _ _
      |>.append 6 0x2384dc4cc14 part0 |>.append 6 0x2384dc4cc14 part1 |>.append 6 0x2384dc4cc14 part2 |>.append 6 0x2375e0fb70e part3
      |>.append 6 0x22c2912582d part4 |>.append 6 0x21665a1b3d7 part5 |>.append 6 0x1f12b6599e5 part6 |>.append 6 0x1b958077b02 part7
      |>.append 6 0x163edc96041 part8 |>.append 4 0xb35e6f7a91 part9)

def receipt : KoalaSplitProof.Receipt envelope split unit :=
  ⟨terminal, plain, boxes, powers, plainPowers, tailPowers, 20773242148615,
    by decide,by decide,loss_bound,fun _ h h' => prices h h', tail⟩

end KoalaAt2428Gate8

#print axioms KoalaAt2428Gate8.loss_bound
#print axioms KoalaAt2428Gate8.receipt
