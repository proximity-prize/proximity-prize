import ProximityPrize.SubmissionLower.KoalaGateSharedData
import ProximityPrize.SubmissionLower.KoalaGateChunkSums
import ProximityPrize.SubmissionLower.KoalaSplitGateWords

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000

set_option linter.defProp false

namespace KoalaAt2428Gate56
open KoalaGateSharedData
open FadicGate KoalaGateCheck
open KoalaWeightedRate (Envelope)
open KoalaFarBridge (rowCheck plainCheck)

def envelope : Envelope :=
  ⟨132,54,2,135,54,3432,4435,⟨3764575509,15118329518,136711181284⟩,1548910286134⟩
abbrev split:ℕ:=48
abbrev unit:ℕ:=1919966501760
abbrev terminal:ℕ:=61
abbrev gate:=KoalaSplitRow.rate envelope split unit

private def boxesTape : List (List Entry) := [
  b05m,b04w,b041,b034,b024,b026,b00z,bzw,
  byp,byq,byr,bxd,bvu,bub,bud,bsz,
  bt1,brz,bs0,bqx,bqw,bps,bpt,bpr,
  bok,bn6,blm,bk4,bih,bfk,bfw,bfx,
  bfy,b4w.take 21,b4y.take 21,b50.take 21,b2c.take 21,b2k.take 21,b2r.take 21]
def boxes (r : ℕ) : List FadicGate.Entry :=
  if r < 22 then [] else boxesTape.getD (r-22) []

def plain : ℕ → ℕ × ℕ × ℕ
  | _ => (0,0,0)

private def powersTape : List String := [
  "","","","","","","","",
  "","","","","","","","",
  "","","","","","","!#","!#%",
  "!#%'",z3p,"!#$(+",z4C,"!#$')/5",z5j,z4Q,"!#$&*-07",
  "!#$&)-17<","!#$&)-187C","!#$&).298EC","!#$&)+349FE","!#$&(+.3:@FE","!#$&(,/3;:GF","!#$&(,/4;;HGD","!#$%(,/4<;JHG",
  "!##%'*057<DJHO","!#$%(*055=>KJH","!##%(+-15>=LKI]","!##%(+-16?>NLKT","!##%'+-16@?HNLL","!##%').17;@BONKb","!##%').287@@QONYk","!##%'*.288A@RQORmk",
  "!!#%&*,248BALRQMfmk","!!#%'*,/29CBFSRP_pmk","!!#%'),/39>CBUSRVrpmk","!!#$'),/3:9DCVUSPkrpm","!!#$&)-/4::EDPVUScurp","!!#$&)-04;:EDJXVU[wus","!!#$&)+047;FFEYXZUpw{","!!#$&(+054<BGF[ZZVjz{",
  "!!#$&(+-15<=HIU_ZVd~#%{","!!#$&(+-15=<IIQ_ZVUv{","!!#$&(+.16=>LII_ZVRh{","!!#$&(,.16@>LIG_ZVRZ{"]

def powers (r : ℕ) : List ℕ :=
  if r=0 then [] else KoalaSplitGateWords.powers (powersTape.getD (r-1) "")

def plainPowers : ℕ → List ℕ
  | _ => []

def tailPowers : List ℕ := KoalaSplitGateWords.powers "!!#$&(+/38;?FJHW]XTPqvme[RJA80'"

def priced (r:ℕ):Bool:=rowCheck gate r (boxes r) (powers r) (plain r) (plainPowers r)
private theorem priced_list : (List.range 60).all (fun i => priced (i+1)) = true := by decide +kernel

theorem prices {r : ℕ} (hr : 0 < r) (hR : r < terminal) : priced r = true :=
  price hr hR priced_list

theorem tail:plainCheck gate terminal (4012,1650,550) tailPowers=true:=by decide +kernel

private abbrev Chunk (i n v : ℕ) := lossChunk 48 envelope plain boxes i n = v
private theorem checkPart (i n v : ℕ) (ok : Chunk i n v := by decide +kernel) : Chunk i n v := ok
private def part0 := checkPart 0 6 0x2384dc4cc14
private def part1 := checkPart 6 6 0x2384dc4cc14
private def part2 := checkPart 12 6 0x2384dc4cc14
private def part3 := checkPart 18 6 0x23676062eb9
private def part4 := checkPart 24 6 0x2295521ea5f
private def part5 := checkPart 30 6 0x2126305ccd7
private def part6 := checkPart 36 6 0x1eb27f6de85
private def part7 := checkPart 42 6 0x1ae826a7fb1
private def part8 := checkPart 48 6 0x1519e582d24
private def part9 := checkPart 54 6 0xe5206a8c6e

theorem loss_bound (N : ℕ) : Bound envelope terminal plain boxes 20802684609011 N :=
  loss_of_chunks 48 envelope terminal plain boxes 20802684609011 N (by decide) (by decide)
    (LossSum.empty _ _ _ _
      |>.append 6 0x2384dc4cc14 part0 |>.append 6 0x2384dc4cc14 part1 |>.append 6 0x2384dc4cc14 part2 |>.append 6 0x23676062eb9 part3
      |>.append 6 0x2295521ea5f part4 |>.append 6 0x2126305ccd7 part5 |>.append 6 0x1eb27f6de85 part6 |>.append 6 0x1ae826a7fb1 part7
      |>.append 6 0x1519e582d24 part8 |>.append 6 0xe5206a8c6e part9)

def receipt : KoalaSplitProof.Receipt envelope split unit :=
  ⟨terminal, plain, boxes, powers, plainPowers, tailPowers, 20802684609011,
    by decide,by decide,loss_bound,fun _ h h' => prices h h', tail⟩

end KoalaAt2428Gate56

#print axioms KoalaAt2428Gate56.loss_bound
#print axioms KoalaAt2428Gate56.receipt
