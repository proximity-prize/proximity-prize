import ProximityPrize.SubmissionLower.KoalaGateSharedData
import ProximityPrize.SubmissionLower.KoalaGateChunkSums
import ProximityPrize.SubmissionLower.KoalaSplitGateWords

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000

set_option linter.defProp false

namespace KoalaAt2428Gate52
open KoalaGateSharedData
open FadicGate KoalaGateCheck
open KoalaWeightedRate (Envelope)
open KoalaFarBridge (rowCheck plainCheck)

def envelope : Envelope :=
  ⟨136,54,2,137,54,3536,4437,⟨3768726533,15447735472,139361687633⟩,1579104692800⟩
abbrev split:ℕ:=48
abbrev unit:ℕ:=1919966465280
abbrev terminal:ℕ:=62
abbrev gate:=KoalaSplitRow.rate envelope split unit

private def boxesTape : List (List Entry) := [
  b05n,b04v,b042,b041,b034,b024,b00x,b00z,
  bzw,byp,byq,byr,bxd,bvu,bub,bud,
  bsz,bt1,brz,bs0,bqx,bqw,bps,bpt,
  bpr,bok,bn6,blm,bii,bih,bfu,bbv,
  bc5,bc7,bc9,bca,bcb,bcc,bcd,bce,
  bcf]
def boxes (r : ℕ) : List FadicGate.Entry :=
  if r < 21 then [] else boxesTape.getD (r-21) []

def plain : ℕ → ℕ × ℕ × ℕ
  | _ => (0,0,0)

private def powersTape : List String := [
  "","","","","","","","",
  "","","","","","","","",
  "","","","","","!#","!#%","!#%",
  "!#%'",z3p,"!#$(+.",z4C,"!#$'*/5",z5j,z4Q,"!#$&*-17",
  "!#$')-18<","!#$&).298D","!#$&).2:9ED","!#$&)+35:GE","!#$&(,/3:@GE","!#$&(,/3;:HG","!#$&(,/4<;IHD","!#$%),05=<KIH",
  "!#$%'*058=DKIQ","!#$%(*065>?LKI","!##%(+-26>>MLJ^","!##%(+-16?>OMLV","!##%'+.17@?IOMN","!##%').27;@CPOLc","!##%'*.287A@RPOZm","!##%'*.288BASRPSom",
  "!!#%'*,348CBMSRNgomj","!!#%'*,/39DCGTSQ`qom","!!#%'),/3:?DBVTSXtqom","!!#$'),/3::DDWVTQltqnm","!!#$&)-04;:EDQWVTewtqt","!!#%&)-04;;FEKYWV^yvtt","!!#$&)+057;GFFZY[Vqy}t","!!#$&(+055<BGG][[Wk{}t",
  "!!#$&(+-25=>HJV`[We~#'}t","!!#$&(+.16==IJR`[WWx}t","!!#$&(,.16>?LJJ`[WSj}t","!!#$&),.27@?LJH`[WS[}t","!!#$&(*.28;?FJHW[WSOot"]

def powers (r : ℕ) : List ℕ :=
  if r=0 then [] else KoalaSplitGateWords.powers (powersTape.getD (r-1) "")

def plainPowers : ℕ → List ℕ
  | _ => []

def tailPowers : List ℕ := KoalaSplitGateWords.powers "!!#$&(+0387?@JHO]XTPdwne[RJA8/"

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
private def part3 := checkPart 18 6 0x2359ec07db2
private def part4 := checkPart 24 6 0x2285f90bd39
private def part5 := checkPart 30 6 0x2109b289803
private def part6 := checkPart 36 6 0x1e7869735f5
private def part7 := checkPart 42 6 0x1a8083a8ac1
private def part8 := checkPart 48 6 0x145c4167871
private def part9 := checkPart 54 6 0xd2f334d52a
private def part10 := checkPart 60 1 0x1953c3ac57

theorem loss_bound (N : ℕ) : Bound envelope terminal plain boxes 20723698037202 N :=
  loss_of_chunks 32 envelope terminal plain boxes 20723698037202 N (by decide) (by decide)
    (LossSum.empty _ _ _ _
      |>.append 6 0x2384dc4cc14 part0 |>.append 6 0x2384dc4cc14 part1 |>.append 6 0x2384dc4cc14 part2 |>.append 6 0x2359ec07db2 part3
      |>.append 6 0x2285f90bd39 part4 |>.append 6 0x2109b289803 part5 |>.append 6 0x1e7869735f5 part6 |>.append 6 0x1a8083a8ac1 part7
      |>.append 6 0x145c4167871 part8 |>.append 6 0xd2f334d52a part9 |>.append 1 0x1953c3ac57 part10)

def receipt : KoalaSplitProof.Receipt envelope split unit :=
  ⟨terminal, plain, boxes, powers, plainPowers, tailPowers, 20723698037202,
    by decide,by decide,loss_bound,fun _ h h' => prices h h', tail⟩

end KoalaAt2428Gate52

#print axioms KoalaAt2428Gate52.loss_bound
#print axioms KoalaAt2428Gate52.receipt
