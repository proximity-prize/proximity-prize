import ProximityPrize.SubmissionLower.KoalaGateSharedData
import ProximityPrize.SubmissionLower.KoalaGateChunkSums
import ProximityPrize.SubmissionLower.KoalaSplitGateWords

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000

set_option linter.defProp false

namespace KoalaAt2428Gate50
open KoalaGateSharedData
open FadicGate KoalaGateCheck
open KoalaWeightedRate (Envelope)
open KoalaFarBridge (rowCheck plainCheck)

def envelope : Envelope :=
  ⟨124,54,4,127,54,3224,4427,⟨9122592176,47588324550,10251660775⟩,3681971938022⟩
abbrev split:ℕ:=48
abbrev unit:ℕ:=1919967703680
abbrev terminal:ℕ:=63
abbrev gate:=KoalaSplitRow.rate envelope split unit

private def boxesTape : List (List Entry) := [
  b05o,b04x,b043,b044,b038,b027,b025,b011,
  bzx,bzy,byu,bxg,bvs,bvv,bu9,bua,
  bt0,bsy,bsz,bs1,brz,br0,bqx,bq0,
  bot,bne,blp,bk5,bie,bifAtom,bfj,bfl,
  bbf,bbd,bbj,bbk,bbm,bbo,bbq,bbs,
  bc2,bc3,b5a,b5b]
def boxes (r : ℕ) : List FadicGate.Entry :=
  if r < 19 then [] else boxesTape.getD (r-19) []

def plain : ℕ → ℕ × ℕ × ℕ
  | _ => (0,0,0)

private def powersTape : List String := [
  "","","","","","","","",
  "","","","","","","","",
  "","","","!#","!#%","!#&","!#%)",z3O,
  z57,"!#%(,1","!#%(-17",z4H,"!#$'+29?","!#$(+2:9G","!#$'+.5:IG","!#$',.3;KI",
  "!#$'*/4<DKL","!#$&*/4=>LK","!#$&*05>=NL]","!#$'*-69>PNS","!#$&)-26?IPN","!#$&)-16@CQPc","!#$&).17A@SQZ","!#$&).28BAUSQs",
  "!#$&(+28=BNUSj","!#$&(,398CHVUb~#%","!#$%(,/59DCXVXz~#%","!#$%),/39EDZXVq~#(~#%","!##%(,/3:FESZXh~#,~#(~#%","!##%(*04;AFM[Z`~##~#,~#(~#%","!##%(+04;<GG^[Zx~#/~#,~#(~#%","!##%(+05<;HG`^[o~#2~#/~#,~#(",
  "!!#%'+-58<IHX`^g~#*~#2~#/~#,~#'","!!#%'+-25=JIRa`^~#!~#6~#2~#/~#,","!!#%'*.16=EJLca`v~#9~#6~#2~#/~#'","!!#%'*.16>@KJecam~#1~#9~#6~#2~#/","!!#%'*.17?>LK_ece~#(~#=~#9~#6~#0","!!#%'*.27??MLWfec}~#@~#=~#9~#0","!!#%'*,27;?NMQhfet~#7~#@~#;~#0","!!#%'),287@INMjhed~#/~#C~#;~#0",
  "!!#%&),/48ADONcie`{~#G~#;~#0","!!#$&),/38AAPNZie`j~#5~#;~#0","!!#$&)-/39BAPNQie`Z~#$~#;~#0","!!#$&)-039BAPNKie`Zp~#;~#0","!!#$&(+049=AJNK`e`Z_~#*~#0~#$","!!#$&(+0498ACNKUe`ZVv~#0~#$"]

def powers (r : ℕ) : List ℕ :=
  if r=0 then [] else KoalaSplitGateWords.powers (powersTape.getD (r-1) "")

def plainPowers : ℕ → List ℕ
  | _ => []

def tailPowers : List ℕ := KoalaSplitGateWords.powers "!!#$&)+04:9A@OLNgb^Xl~#7~#,~!~sg[PE:/"

def priced (r:ℕ):Bool:=rowCheck gate r (boxes r) (powers r) (plain r) (plainPowers r)
private theorem priced_list : (List.range 62).all (fun i => priced (i+1)) = true := by decide +kernel

theorem prices {r : ℕ} (hr : 0 < r) (hR : r < terminal) : priced r = true :=
  price hr hR priced_list

theorem tail:plainCheck gate terminal (4012,1650,550) tailPowers=true:=by decide +kernel

private abbrev Chunk (i n v : ℕ) := lossChunk 24 envelope plain boxes i n = v
private theorem checkPart (i n v : ℕ) (ok : Chunk i n v := by decide +kernel) : Chunk i n v := ok
private def part0 := checkPart 0 6 0x2384dc4cc14
private def part1 := checkPart 6 6 0x2384dc4cc14
private def part2 := checkPart 12 6 0x2384dc4cc14
private def part3 := checkPart 18 6 0x233cd1ee49c
private def part4 := checkPart 24 6 0x2272cc2ce3f
private def part5 := checkPart 30 6 0x20edb3036fd
private def part6 := checkPart 36 6 0x1e75a3905a3
private def part7 := checkPart 42 6 0x1a5cac7fb72
private def part8 := checkPart 48 6 0x1467fd18759
private def part9 := checkPart 54 6 0xd4270ac6e2
private def part10 := checkPart 60 2 0x303595bc67

theorem loss_bound (N : ℕ) : Bound envelope terminal plain boxes 20799449946571 N :=
  loss_of_chunks 24 envelope terminal plain boxes 20799449946571 N (by decide) (by decide)
    (LossSum.empty _ _ _ _
      |>.append 6 0x2384dc4cc14 part0 |>.append 6 0x2384dc4cc14 part1 |>.append 6 0x2384dc4cc14 part2 |>.append 6 0x233cd1ee49c part3
      |>.append 6 0x2272cc2ce3f part4 |>.append 6 0x20edb3036fd part5 |>.append 6 0x1e75a3905a3 part6 |>.append 6 0x1a5cac7fb72 part7
      |>.append 6 0x1467fd18759 part8 |>.append 6 0xd4270ac6e2 part9 |>.append 2 0x303595bc67 part10)

def receipt : KoalaSplitProof.Receipt envelope split unit :=
  ⟨terminal, plain, boxes, powers, plainPowers, tailPowers, 20799449946571,
    by decide,by decide,loss_bound,fun _ h h' => prices h h', tail⟩

end KoalaAt2428Gate50

#print axioms KoalaAt2428Gate50.loss_bound
#print axioms KoalaAt2428Gate50.receipt
