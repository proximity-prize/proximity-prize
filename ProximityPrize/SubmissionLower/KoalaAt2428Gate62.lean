import ProximityPrize.SubmissionLower.KoalaGateSharedData
import ProximityPrize.SubmissionLower.KoalaGateChunkSums
import ProximityPrize.SubmissionLower.KoalaSplitGateWords

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000

set_option linter.defProp false

namespace KoalaAt2428Gate62
open KoalaGateSharedData
open FadicGate KoalaGateCheck
open KoalaWeightedRate (Envelope)
open KoalaFarBridge (rowCheck plainCheck)

def envelope : Envelope :=
  ⟨136,47,8,136,47,3536,4436,⟨6640920162,46545539306,6986373022⟩,2995181592547⟩
abbrev split:ℕ:=48
abbrev unit:ℕ:=1919968010880
abbrev terminal:ℕ:=59
abbrev gate:=KoalaSplitRow.rate envelope split unit

private def boxesTape : List (List Entry) := [
  b05m,b04w,b041,b034,b024,b026,b00z,b012,
  byp,byq,byr,bxd,bvu,bub,bud,bsz,
  bt1,brz,bs0,bqx,bqw,bqy,bpt,bpr,
  bok,bn6,blm,bk4,bih,bfk,bfv,b7f.take 21,
  b7w.take 21,b86.take 21,b8l.take 21,b8s.take 21,b96.take 21]
def boxes (r : ℕ) : List FadicGate.Entry :=
  if r < 22 then [] else boxesTape.getD (r-22) []

def plain : ℕ → ℕ × ℕ × ℕ
  | _ => (0,0,0)

private def powersTape : List String := [
  "","","","","","","","",
  "","","","","","","","",
  "","","","","","","!#","!#%",
  "!#%'",z3p,"!#$(+",z4C,"!#$'*0","!#$'*076","!#$&*-27","!#$&+-18",
  "!#$')-29>","!#$&).2:9F","!#$&).3::HF","!#$&)+35:IH","!#$&(,/3;CIH","!#$&(,/4<<KI","!#$&(,/4=<LKJ","!#$%)-05>=NLJ",
  "!#$%'*069>GNLY","!#$%(+166?AONP","!##%(+-26@?POM","!##%(+-17@@RPO_","!##%'+.17A@KRPU","!##%').28<AESROm","!##%'*.288BAUSRey","!##%'*/398CBVUS[|y",
  "!!#%'*,359DCPVURs|y","!!#%'*,/39EDIXVTj~!~|y","!!#%'),/3:@EDYXVb~#$~!~|y","!!#$'),/4;:EEZYXXy~#$~!~{","!!#$&)-04;;FETZYVp~#'~#$~!~","!!#%&)-04<;GFN][Yg~#*~#'~#$","!!#$&)+057<HGG^]Z^~!~~#)~#%","!!#$&(+155<CHG`_ZVt~#,~#%",
  "!!#$&(+-25=>IHY_ZVe~#.~#%","!!#$&(+.16==JHP_ZVT{~#%"]

def powers (r : ℕ) : List ℕ :=
  if r=0 then [] else KoalaSplitGateWords.powers (powersTape.getD (r-1) "")

def plainPowers : ℕ → List ℕ
  | _ => []

def tailPowers : List ℕ := KoalaSplitGateWords.powers "!!#$')-/28@?MKMeb^Z~#!~#:~#1~#)}uld[~#w~%F"

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
private def part3 := checkPart 18 6 0x2369c6d462f
private def part4 := checkPart 24 6 0x22acc4ba795
private def part5 := checkPart 30 6 0x2158d4d907a
private def part6 := checkPart 36 6 0x1f1ab58ba9d
private def part7 := checkPart 42 6 0x1ba81b3e3c1
private def part8 := checkPart 48 6 0x1657173343a
private def part9 := checkPart 54 4 0xb667e180b6

theorem loss_bound (N : ℕ) : Bound envelope terminal plain boxes 20787200669128 N :=
  loss_of_chunks 48 envelope terminal plain boxes 20787200669128 N (by decide) (by decide)
    (LossSum.empty _ _ _ _
      |>.append 6 0x2384dc4cc14 part0 |>.append 6 0x2384dc4cc14 part1 |>.append 6 0x2384dc4cc14 part2 |>.append 6 0x2369c6d462f part3
      |>.append 6 0x22acc4ba795 part4 |>.append 6 0x2158d4d907a part5 |>.append 6 0x1f1ab58ba9d part6 |>.append 6 0x1ba81b3e3c1 part7
      |>.append 6 0x1657173343a part8 |>.append 4 0xb667e180b6 part9)

def receipt : KoalaSplitProof.Receipt envelope split unit :=
  ⟨terminal, plain, boxes, powers, plainPowers, tailPowers, 20787200669128,
    by decide,by decide,loss_bound,fun _ h h' => prices h h', tail⟩

end KoalaAt2428Gate62

#print axioms KoalaAt2428Gate62.loss_bound
#print axioms KoalaAt2428Gate62.receipt
