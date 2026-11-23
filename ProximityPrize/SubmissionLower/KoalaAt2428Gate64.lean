import ProximityPrize.SubmissionLower.KoalaGateSharedData
import ProximityPrize.SubmissionLower.FadicRisingGate
import ProximityPrize.SubmissionLower.KoalaSplitGateWords

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000

set_option linter.defProp false

namespace KoalaAt2428Gate64
open KoalaGateSharedData
open FadicGate KoalaGateCheck
open KoalaWeightedRate (Envelope)
open KoalaFarBridge (rowCheck plainCheck)

def envelope : Envelope :=
  ⟨136,52,3,137,52,3536,4437,⟨8352908319,49858435394,14033614975⟩,3694304759891⟩
abbrev split:ℕ:=48
abbrev unit:ℕ:=1919968659840
abbrev terminal:ℕ:=65
abbrev gate:=KoalaSplitRow.rate envelope split unit

private def boxesTape : List (List Entry) := [
  b05k,b04t,b040,b03z,b033,b022,b010,b00w,
  bzz,bzv,bys,bxc,bxb,bvt,bvs,buc,
  bu9,bt2,bt0,bsy,br2,bpw,boq,bnc,
  bn5,bll,blk,bk3,bk2,big,bie,bfm,
  bfj,bbb,bbc,b5o,b4s,b4t,b4v,b4x,
  b4z,b4l,b4m,b4n,b4o,b4p,b4q,b4r]
def boxes (r : ℕ) : List FadicGate.Entry :=
  if r < 17 then [] else boxesTape.getD (r-17) []

def plain : ℕ → ℕ × ℕ × ℕ
  | _ => (0,0,0)

private def powersTape : List String := [
  "","","","","","","","",
  "","","","","","","","",
  "","!#","!#&","!#&","!#%+",z4E,z4D,"!#%)05",
  "!#%(,6;",z4I,"!#%)-17E","!#%'-18FE","!#$(+29@F","!#%(+3::HG","!#$'+/6:JH","!#$',/3<KJV",
  "!#$'*/4<EKN","!#$&*05=?MKg","!#$'*05>=OM^","!#$'+-6:>POU","!#$&)-26?JPOnv","!#$&)-17@DRPezv","!#$&).17A@TR]}zv","!#$&*.28BAVTTt}zv",
  "!#$&(,29>BOVTl~##}z","!#$&(,399CIWVd~#'~##}z","!#$%),/59DCYW[{~#'~##}","!#$%),/3:ED[YWs~#*~#'~##z","!##&(-/4;GET[Yk~#.~#*~#'~##","!#$%(+04;BGN][b~#%~#.~#*~#'z","!##%(+05<=GH_][z~#1~#.~#*~#'","!##%(+05=<HGa_]r~#4~#1~#.~#*z",
  "!!#%'+-68=IHZa_i~#,~#4~#1~#.~#(","!!#%'+.26=KIScaa~#$~#8~#4~#1~#.z","!!#%'*.16>FKMdcay~#;~#8~#4~#1~#'","!!#%'*.16>@KKfdcp~#3~#;~#8~#3~#/y","!!#%'*.27?>LK`fdg~#+~#?~#;~#6~#0~#$","!!#%'*/27@?NLXhfd~#!~#B~#>~#:~#0~#$","!!#%'*,28<@ONRihev~#9~#A~#<~#0~#$","!!#%'),388@JONkief~#0~#D~#<~#0~#$",
  "!!#%&),058AEPNeje`|~#G~#<~#0~#$","!!#$&)-/39BAQN[je`k~#6~#<~#0~#$","!!#$&)-039BAQNRje`[~#%~#<~#0~#$","!!#$')-04:CAQNLje`[q~#<~#0~#$","!!#$&(+04:>AJNLae`[_~#*~#0~#$","!!#$&(+04:9ADNLVe`[Vv~#0~#$","!!#$&)+04:9A@NLMe`[Ve~#0~#$","!!#$&)+-469A@NLIe`[VR{~#$"]

def powers (r : ℕ) : List ℕ :=
  if r=0 then [] else KoalaSplitGateWords.powers (powersTape.getD (r-1) "")

def plainPowers : ℕ → List ℕ
  | _ => []

def tailPowers : List ℕ := KoalaSplitGateWords.powers "!!#$&),-149BAPMK_d_ZUt~#/~##ui^QF<"

def priced (r:ℕ):Bool:=rowCheck gate r (boxes r) (powers r) (plain r) (plainPowers r)
private theorem priced_list : (List.range 64).all (fun i => priced (i+1)) = true := by decide +kernel

theorem prices {r : ℕ} (hr : 0 < r) (hR : r < terminal) : priced r = true :=
  price hr hR priced_list

theorem tail:plainCheck gate terminal (4012,1650,550) tailPowers=true:=by decide +kernel

private abbrev Chunk (i n v : ℕ) := lossChunk 16 envelope plain boxes i n = v
private theorem checkPart (i n v : ℕ) (ok : Chunk i n v := by
    unfold Chunk
    rw [← KoalaGateCheck.lossChunkRising_eq]
    decide +kernel) : Chunk i n v := ok
private def part0 := checkPart 0 6 0x2384dc4cc14
private def part1 := checkPart 6 6 0x2384dc4cc14
private def part2 := checkPart 12 6 0x237e29ab8f0
private def part3 := checkPart 18 6 0x23263126425
private def part4 := checkPart 24 6 0x225a176e6ec
private def part5 := checkPart 30 6 0x20ddaa0431d
private def part6 := checkPart 36 6 0x1e38d1ebbef
private def part7 := checkPart 42 6 0x1a21fa3fd6d
private def part8 := checkPart 48 6 0x141c794a639
private def part9 := checkPart 54 6 0xcd1c8c52e3
private def part10 := checkPart 60 4 0x5274f3ab53

theorem loss_bound (N : ℕ) : Bound envelope terminal plain boxes 20845139672337 N :=
  loss_of_chunks 16 envelope terminal plain boxes 20845139672337 N (by decide) (by decide)
    (LossSum.empty _ _ _ _
      |>.append 6 0x2384dc4cc14 part0 |>.append 6 0x2384dc4cc14 part1 |>.append 6 0x237e29ab8f0 part2 |>.append 6 0x23263126425 part3
      |>.append 6 0x225a176e6ec part4 |>.append 6 0x20ddaa0431d part5 |>.append 6 0x1e38d1ebbef part6 |>.append 6 0x1a21fa3fd6d part7
      |>.append 6 0x141c794a639 part8 |>.append 6 0xcd1c8c52e3 part9 |>.append 4 0x5274f3ab53 part10)

def receipt : KoalaSplitProof.Receipt envelope split unit :=
  ⟨terminal, plain, boxes, powers, plainPowers, tailPowers, 20845139672337,
    by decide,by decide,loss_bound,fun _ h h' => prices h h', tail⟩

end KoalaAt2428Gate64

#print axioms KoalaAt2428Gate64.loss_bound
#print axioms KoalaAt2428Gate64.receipt
