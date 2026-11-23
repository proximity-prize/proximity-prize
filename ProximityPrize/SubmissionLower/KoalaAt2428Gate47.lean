import ProximityPrize.SubmissionLower.KoalaGateSharedData
import ProximityPrize.SubmissionLower.KoalaGateChunkSums
import ProximityPrize.SubmissionLower.KoalaSplitGateWords

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000

set_option linter.defProp false

namespace KoalaAt2428Gate47
open KoalaGateSharedData
open FadicGate KoalaGateCheck
open KoalaWeightedRate (Envelope)
open KoalaFarBridge (rowCheck plainCheck)

def envelope : Envelope :=
  ⟨136,55,2,137,55,3536,4437,⟨3932971202,15674169215,145297094500⟩,1640535071560⟩
abbrev split:ℕ:=48
abbrev unit:ℕ:=1919966394240
abbrev terminal:ℕ:=64
abbrev gate:=KoalaSplitRow.rate envelope split unit

private def boxesTape : List (List Entry) := [
  b05p,b04y,b044,b042,b036,b025,b011,b00x,
  bzy,bzw,byp,byq,bxe,bvw,bua,bub,
  bsy,bsz,bs1,brz,bs0,bqx,bqw,bps,
  bon,bn8,blo,bk6,bifAtom,bii,bfl,bfu,
  bbv,bc5,bc7,bc9,bca,bcb,bcc,bcd,
  bce,bcf,b33.take 22,b39.take 22]
def boxes (r : ℕ) : List FadicGate.Entry :=
  if r < 20 then [] else boxesTape.getD (r-20) []

def plain : ℕ → ℕ × ℕ × ℕ
  | _ => (0,0,0)

private def powersTape : List String := [
  "","","","","","","","",
  "","","","","","","","",
  "","","","","!#","!#%","!#%","!#%)",
  z3p,"!#%(+.","!#$(,/","!#$',/5",z65,"!#$'*176","!#$&*-27","!#$'+-18D",
  "!#$').29>D","!#$&).298ED","!#$&).3:9GE","!#$&*,45:HGD","!#$&(,/4;BHG","!#$&(,/4<<IHN","!#$&),05=<KIG","!#$%)-05>=LKI",
  "!#$%(+069>FLKT","!#$&(+166?@NLM","!##%(+-26??ONLa","!##%(+.17@?QONYk","!##%'+.28A@JQOQmk","!##%'*.28<AERQMfmk","!##%'*/398BATRQ_pmk","!##%'*/399CBUTRWrpmk",
  "!!#%'*,359DCOUTPkrpm","!!#%'*,03:EDIVUSdurpm","!!#%')-/4:@EDXVU]wurp","!!#$')-04;;FEYXVUpwurp","!!#%&)-05<;FFSYXUizwuw","!!#%&)-05<<GFM[YXb|zxw","!!#$&*+158<HHH][_[u|~##w","!!#$'(+165=DIH_^_Yo~#!~##w",
  "!!#$&(+.26>?JKYc_Yj~#+~##w","!!#$&),.16>>KKUc_Y[|~##w","!!#$&),.27?@NKLc_YUn~##w","!!#$&),/27A@NKIc_YU`~##w","!!#$&(*/39=@HKIY_YUQsw","!!#$&(+/498@AKIQ_YUQew","!!#$&(+0498@>KIH_YUQVw"]

def powers (r : ℕ) : List ℕ :=
  if r=0 then [] else KoalaSplitGateWords.powers (powersTape.getD (r-1) "")

def plainPowers : ℕ → List ℕ
  | _ => []

def tailPowers : List ℕ := KoalaSplitGateWords.powers "!!#$&)+-458@>KIG_YUQMindZQG>4+"

def priced (r:ℕ):Bool:=rowCheck gate r (boxes r) (powers r) (plain r) (plainPowers r)
private theorem priced_list : (List.range 63).all (fun i => priced (i+1)) = true := by decide +kernel

theorem prices {r : ℕ} (hr : 0 < r) (hR : r < terminal) : priced r = true :=
  price hr hR priced_list

theorem tail:plainCheck gate terminal (4012,1650,550) tailPowers=true:=by decide +kernel

private abbrev Chunk (i n v : ℕ) := lossChunk 32 envelope plain boxes i n = v
private theorem checkPart (i n v : ℕ) (ok : Chunk i n v := by decide +kernel) : Chunk i n v := ok
private def part0 := checkPart 0 6 0x2384dc4cc14
private def part1 := checkPart 6 6 0x2384dc4cc14
private def part2 := checkPart 12 6 0x2384dc4cc14
private def part3 := checkPart 18 6 0x234b0195b28
private def part4 := checkPart 24 6 0x2277bacaed9
private def part5 := checkPart 30 6 0x20f1d483ce4
private def part6 := checkPart 36 6 0x1e642f94533
private def part7 := checkPart 42 6 0x1a40294431d
private def part8 := checkPart 48 6 0x14259b1ab9f
private def part9 := checkPart 54 6 0xce4c1a86ff
private def part10 := checkPart 60 3 0x4247221629

theorem loss_bound (N : ℕ) : Bound envelope terminal plain boxes 20827988327480 N :=
  loss_of_chunks 32 envelope terminal plain boxes 20827988327480 N (by decide) (by decide)
    (LossSum.empty _ _ _ _
      |>.append 6 0x2384dc4cc14 part0 |>.append 6 0x2384dc4cc14 part1 |>.append 6 0x2384dc4cc14 part2 |>.append 6 0x234b0195b28 part3
      |>.append 6 0x2277bacaed9 part4 |>.append 6 0x20f1d483ce4 part5 |>.append 6 0x1e642f94533 part6 |>.append 6 0x1a40294431d part7
      |>.append 6 0x14259b1ab9f part8 |>.append 6 0xce4c1a86ff part9 |>.append 3 0x4247221629 part10)

def receipt : KoalaSplitProof.Receipt envelope split unit :=
  ⟨terminal, plain, boxes, powers, plainPowers, tailPowers, 20827988327480,
    by decide,by decide,loss_bound,fun _ h h' => prices h h', tail⟩

end KoalaAt2428Gate47

#print axioms KoalaAt2428Gate47.loss_bound
#print axioms KoalaAt2428Gate47.receipt
