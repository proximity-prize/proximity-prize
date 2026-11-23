import ProximityPrize.SubmissionLower.KoalaGateSharedData
import ProximityPrize.SubmissionLower.KoalaGateChunkSums
import ProximityPrize.SubmissionLower.KoalaSplitGateWords

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000

set_option linter.defProp false

namespace KoalaAt2428Gate5
open KoalaGateSharedData
open FadicGate KoalaGateCheck
open KoalaWeightedRate (Envelope)
open KoalaFarBridge (rowCheck plainCheck)

def envelope : Envelope :=
  ⟨113,54,13,114,54,2938,4314,⟨9086520650,40836914630,7435749656⟩,3201793424786⟩
abbrev split:ℕ:=32
abbrev unit:ℕ:=1920000000000
abbrev terminal:ℕ:=57
abbrev gate:=KoalaSplitRow.rate envelope split unit

private def boxesTape : List (List Entry) := [
  b054,b046,b04a,b03f,b02d,b014,b016,b005,
  byx,bxf,bxi,bxl,bw0,buh,bt5,bs3,
  bs4,bqy,br3,bpr,bpy,bpv,bom,bop,
  bnb,bn7,blr,blu,bk9,bio,biq]
def boxes (r : ℕ) : List FadicGate.Entry :=
  if r < 26 then [] else boxesTape.getD (r-26) []

def plain : ℕ → ℕ × ℕ × ℕ
  | _ => (0,0,0)

private def powersTape : List String := [
  "","","","","","","","",
  "","","","","","","","",
  "","","","","","","","",
  "","!#","!#$","!#$","!#$&","!#$')",z5T,z5T,
  "!!$&(-1","!!$%(-19","!!#&).2:9","!!#&)+35:","!!#%(+.3;","!!#%(+.3;<","!!#%(,/4<;K","!!#%(,/4=<MK",
  "!!#%'*/58=FMK","!!#%'*055>@NM","!!#%'*,15?>PNL","!!#%'*-06??QPN","!!#%&*-06@?KQPU","!!#$&)-17;@DRQN","!!#$')-177A@TRQ","!!#$').287BAUTR[",
  "!!#$&)+248CBOUTR","!!#$&)+.28DCHWUTk","!!#$&(+.29>DCXWUb","!!#$&(,.399DDZXWXy","!!#$&(,/3:9EDSZXVp","!!#$&(,/3;:FEL[YXg~#+","!!#$&(*/46;GFF][Y^~!~~#*","!!#$&'*044;BGF_]YUu~#-"]
def powers (r : ℕ) : List ℕ :=
  if r=0 then [] else KoalaSplitGateWords.powers (powersTape.getD (r-1) "")

def plainPowers : ℕ → List ℕ
  | _ => []

def tailPowers:List ℕ:=KoalaSplitGateWords.powers "!!#$&(+.36>?JH[b^Yp~#;~#2~#)}tkbX~#j~%A~%S~$E"

def priced (r:ℕ):Bool:=rowCheck gate r (boxes r) (powers r) (plain r) (plainPowers r)
private theorem priced_list : (List.range 56).all (fun i => priced (i+1)) = true := by decide +kernel

theorem prices {r : ℕ} (hr : 0 < r) (hR : r < terminal) : priced r = true :=
  price hr hR priced_list

theorem tail:plainCheck gate terminal (4012,1650,550) tailPowers=true:=by decide +kernel

private abbrev Chunk (i n v : ℕ) := lossChunk 96 envelope plain boxes i n = v
private theorem checkPart (i n v : ℕ) (ok : Chunk i n v := by decide +kernel) : Chunk i n v := ok
private def part0 := checkPart 0 6 0x2384dc4cc14
private def part1 := checkPart 6 6 0x2384dc4cc14
private def part2 := checkPart 12 6 0x2384dc4cc14
private def part3 := checkPart 18 6 0x2384dc4cc14
private def part4 := checkPart 24 6 0x230981f7f64
private def part5 := checkPart 30 6 0x21b77aaf5fc
private def part6 := checkPart 36 6 0x1f9cfe408aa
private def part7 := checkPart 42 6 0x1c549383546
private def part8 := checkPart 48 6 0x179be2596f1
private def part9 := checkPart 54 2 0x6838844942

theorem loss_bound (N : ℕ) : Bound envelope terminal plain boxes 20677426136019 N :=
  loss_of_chunks 96 envelope terminal plain boxes 20677426136019 N (by decide) (by decide)
    (LossSum.empty _ _ _ _
      |>.append 6 0x2384dc4cc14 part0 |>.append 6 0x2384dc4cc14 part1 |>.append 6 0x2384dc4cc14 part2 |>.append 6 0x2384dc4cc14 part3
      |>.append 6 0x230981f7f64 part4 |>.append 6 0x21b77aaf5fc part5 |>.append 6 0x1f9cfe408aa part6 |>.append 6 0x1c549383546 part7
      |>.append 6 0x179be2596f1 part8 |>.append 2 0x6838844942 part9)

def receipt : KoalaSplitProof.Receipt envelope split unit :=
  ⟨terminal, plain, boxes, powers, plainPowers, tailPowers, 20677426136019,
    by decide,by decide,loss_bound,fun _ h h' => prices h h', tail⟩

end KoalaAt2428Gate5

#print axioms KoalaAt2428Gate5.loss_bound
#print axioms KoalaAt2428Gate5.receipt
