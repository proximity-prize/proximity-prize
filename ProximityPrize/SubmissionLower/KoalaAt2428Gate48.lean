import ProximityPrize.SubmissionLower.KoalaGateSharedData
import ProximityPrize.SubmissionLower.FadicRisingGate
import ProximityPrize.SubmissionLower.KoalaSplitGateWords

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000

set_option linter.defProp false

namespace KoalaAt2428Gate48
open KoalaGateSharedData
open FadicGate KoalaGateCheck
open KoalaWeightedRate (Envelope)
open KoalaFarBridge (rowCheck plainCheck)

def envelope : Envelope :=
  ⟨116,56,4,119,56,3016,4419,⟨10161480997,45502641844,11648140203⟩,3744369347089⟩
abbrev split:ℕ:=48
abbrev unit:ℕ:=1919967922560
abbrev terminal:ℕ:=64
abbrev gate:=KoalaSplitRow.rate envelope split unit

private def boxesTape : List (List Entry) := [
  b05o,b04x,b043,b035,b038,b027,b00y,bzv,
  bzx,bzy,byu,bxg,bvs,bvv,bu9,bua,
  bt0,bsy,bs2,bs1,brz,br0,bpz,bos,
  bnd,bln,bk2,bk5,bie,bifAtom,bfj,bfl,
  bbf,bbi,bbg,bbh,b5r,b5s,b5u,b5v,
  b5w,b5x,b5y,b5z,b60]
def boxes (r : ℕ) : List FadicGate.Entry :=
  if r < 19 then [] else boxesTape.getD (r-19) []

def plain : ℕ → ℕ × ℕ × ℕ
  | _ => (0,0,0)

private def powersTape : List String := [
  "","","","","","","","",
  "","","","","","","","",
  "","","","!#","!#%","!#&)","!#%)",z3O,
  "!#%(,6",z4I,"!#%)-17",z4H,"!#$(+29@","!#%(+3::H","!#$'+/5:JH","!#$',/3;KJ",
  "!#$'*/4<EKN","!#$&*05=?MK","!#$'*05>=OM_","!#$'*-69>POU","!#$&)-26?JPOn","!#$&)-17@DRPe","!#$&).17A@TR]","!#$&*.28BAVTTu",
  "!#$&(,29=BOVTl~##","!#$&(,399CIWVd~#'~##","!#$%),/59DCYW[|~#'~##","!#$%),/3:ED[YWs~#+~#'~##","!##&(-/4;FET[Yk~#.~#+~#'~##","!#$%(*04;AFN][b~#%~#.~#+~#'","!##%(+05<<GH_][z~#1~#.~#+~#'","!##%(+05<<HGa_]r~#5~#1~#.~#+",
  "!!#%'+-58<IHZa_i~#,~#5~#1~#.~#)","!!#%'+.25=JIScaa~#$~#8~#5~#1~#.","!!#%'*.16>EJMdcay~#<~#8~#5~#1~#)","!!#%'*.16>@KJfdcp~#4~#<~#8~#5~#.","!!#%'*.27?>LK`fdh~#+~#?~#<~#8~#/","!!#%'*/27@?MLXhfd~#!~#C~#?~#:~#/","!!#%'*,28<@NMRigeu~#:~#B~#;~#/~##","!!#%'),388@INMkhed~#/~#E~#;~#/~##",
  "!!#%&),058ADONdie`{~#G~#;~#/~##","!!#$&)-/39BAPNZie`j~#5~#;~#/~##","!!#$&)-/39BAPNQie`Z~#$~#;~#/~##","!!#$')-049CAPNKie`Zo~#;~#/~##","!!#$&(+04:>AJNK`e`Z^~#)~#/~##","!!#$&(+04:9ACNKVe`ZUu~#/~##","!!#$&(+04:9A?NKLe`ZUd~#/~##"]

def powers (r : ℕ) : List ℕ :=
  if r=0 then [] else KoalaSplitGateWords.powers (powersTape.getD (r-1) "")

def plainPowers : ℕ → List ℕ
  | _ => []

def tailPowers : List ℕ := KoalaSplitGateWords.powers "!!#$&)+-469B@OMJhc_Y[~#'~#-~#!th]PE9"

def priced (r:ℕ):Bool:=rowCheck gate r (boxes r) (powers r) (plain r) (plainPowers r)
private theorem priced_list : (List.range 63).all (fun i => priced (i+1)) = true := by decide +kernel

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
private def part2 := checkPart 12 6 0x2384dc4cc14
private def part3 := checkPart 18 6 0x2337f709d52
private def part4 := checkPart 24 6 0x2265987a263
private def part5 := checkPart 30 6 0x20db4876568
private def part6 := checkPart 36 6 0x1e48e727989
private def part7 := checkPart 42 6 0x1a12729f101
private def part8 := checkPart 48 6 0x13fcb978074
private def part9 := checkPart 54 6 0xcaf44b9474
private def part10 := checkPart 60 3 0x409504a420

theorem loss_bound (N : ℕ) : Bound envelope terminal plain boxes 20759746587883 N :=
  loss_of_chunks 16 envelope terminal plain boxes 20759746587883 N (by decide) (by decide)
    (LossSum.empty _ _ _ _
      |>.append 6 0x2384dc4cc14 part0 |>.append 6 0x2384dc4cc14 part1 |>.append 6 0x2384dc4cc14 part2 |>.append 6 0x2337f709d52 part3
      |>.append 6 0x2265987a263 part4 |>.append 6 0x20db4876568 part5 |>.append 6 0x1e48e727989 part6 |>.append 6 0x1a12729f101 part7
      |>.append 6 0x13fcb978074 part8 |>.append 6 0xcaf44b9474 part9 |>.append 3 0x409504a420 part10)

def receipt : KoalaSplitProof.Receipt envelope split unit :=
  ⟨terminal, plain, boxes, powers, plainPowers, tailPowers, 20759746587883,
    by decide,by decide,loss_bound,fun _ h h' => prices h h', tail⟩

end KoalaAt2428Gate48

#print axioms KoalaAt2428Gate48.loss_bound
#print axioms KoalaAt2428Gate48.receipt
