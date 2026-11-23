import ProximityPrize.SubmissionLower.KoalaGateSharedData
import ProximityPrize.SubmissionLower.FadicRisingGate
import ProximityPrize.SubmissionLower.KoalaSplitGateWords

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000

set_option linter.defProp false

namespace KoalaAt2428Gate49
open KoalaGateSharedData
open FadicGate KoalaGateCheck
open KoalaWeightedRate (Envelope)
open KoalaFarBridge (rowCheck plainCheck)

def envelope : Envelope :=
  ⟨120,55,4,123,55,3120,4423,⟨9634391940,46622047054,10936235725⟩,3719412206524⟩
abbrev split:ℕ:=48
abbrev unit:ℕ:=1919967920640
abbrev terminal:ℕ:=64
abbrev gate:=KoalaSplitRow.rate envelope split unit

private def boxesTape : List (List Entry) := [
  b05o,b04x,b043,b035,b038,b027,b00y,bzv,
  bzx,bzy,byu,bxg,bvs,bvv,bu9,bua,
  bt0,bsy,bs2,bs1,brz,br0,bpz,bos,
  bnd,bln,bk2,bk5,bie,bifAtom,bfj,bfl,
  bbf,bbd,b5q,b5c,b5d,b5e,b5f,b5g,
  b5h,b5i,b5a,b5b,b5j]
def boxes (r : ℕ) : List FadicGate.Entry :=
  if r < 19 then [] else boxesTape.getD (r-19) []

def plain : ℕ → ℕ × ℕ × ℕ
  | _ => (0,0,0)

private def powersTape : List String := [
  "","","","","","","","",
  "","","","","","","","",
  "","","","!#","!#%","!#&)","!#%)",z3O,
  "!#%(,6",z4I,"!#%(-17",z4H,"!#$(+29@","!#%(+3:9H","!#$'+.5:IH","!#$',/3;KI",
  "!#$'*/4<EKM","!#$&*05=>MK","!#$&*05>=NM^","!#$'*-69>PNT","!#$&)-26?JPNm","!#$&)-16@DRPe","!#$&).17A@SR[","!#$&).28BAUSSt",
  "!#$&(+28=BOUSk~##","!#$&(,398CIWUc~#&~##","!#$%),/59DCYWZ{~#&~##","!#$%),/3:EDZYWr~#*~#&~##","!##&(,/4:FETZYj~#-~#*~#&~##","!##%(*04;AFN]Za~#$~#-~#*~#&","!##%(+04<<GG_]Zy~#0~#-~#*~#&","!##%(+05<<HG`_]q~#4~#0~#-~#*",
  "!!#%'+-58<IHY`_h~#+~#4~#0~#-~#(","!!#%'+-25=JISb``~##~#7~#4~#0~#-","!!#%'*.16>EJLdb`x~#;~#7~#4~#0~#(","!!#%'*.16>@KJedbo~#2~#;~#7~#4~#0","!!#%'*.27?>LK_edf~#*~#>~#;~#7~#1~#%","!!#%'*.27@?MLXgec~!~~#A~#>~#;~#1~#%","!!#%'*,28;@NMQigev~#9~#A~#=~#1~#%","!!#%'),388@INMjief~#0~#E~#=~#1~#%",
  "!!#%&),/48ADONdje`}~#H~#=~#1~#%","!!#$&)-/38AAPN[je`k~#7~#=~#1~#%","!!#$&)-/39BAPNQje`[~#&~#=~#1~#%","!!#$')-049CAPNKje`[q~#=~#1~#%","!!#$&(+04:>AJNK`e`[`~#+~#1~#%","!!#$&(+04:9ACNKVe`[Vw~#1~#%","!!#$&(+04:9A?NKLe`[Vf~#1~#%"]

def powers (r : ℕ) : List ℕ :=
  if r=0 then [] else KoalaSplitGateWords.powers (powersTape.getD (r-1) "")

def plainPowers : ℕ → List ℕ
  | _ => []

def tailPowers : List ℕ := KoalaSplitGateWords.powers "!!#$&)+-469B@OLJgc^YZ~#'~#-~!~sh[PE9."

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
private def part3 := checkPart 18 6 0x23384e584fa
private def part4 := checkPart 24 6 0x2266e12eedd
private def part5 := checkPart 30 6 0x20de5e81b41
private def part6 := checkPart 36 6 0x1e4f086ffd2
private def part7 := checkPart 42 6 0x1a1daa3cd25
private def part8 := checkPart 48 6 0x1407ea4b6f8
private def part9 := checkPart 54 6 0xca5766d1bd
private def part10 := checkPart 60 3 0x3f756d789e

theorem loss_bound (N : ℕ) : Bound envelope terminal plain boxes 20761214632350 N :=
  loss_of_chunks 16 envelope terminal plain boxes 20761214632350 N (by decide) (by decide)
    (LossSum.empty _ _ _ _
      |>.append 6 0x2384dc4cc14 part0 |>.append 6 0x2384dc4cc14 part1 |>.append 6 0x2384dc4cc14 part2 |>.append 6 0x23384e584fa part3
      |>.append 6 0x2266e12eedd part4 |>.append 6 0x20de5e81b41 part5 |>.append 6 0x1e4f086ffd2 part6 |>.append 6 0x1a1daa3cd25 part7
      |>.append 6 0x1407ea4b6f8 part8 |>.append 6 0xca5766d1bd part9 |>.append 3 0x3f756d789e part10)

def receipt : KoalaSplitProof.Receipt envelope split unit :=
  ⟨terminal, plain, boxes, powers, plainPowers, tailPowers, 20761214632350,
    by decide,by decide,loss_bound,fun _ h h' => prices h h', tail⟩

end KoalaAt2428Gate49

#print axioms KoalaAt2428Gate49.loss_bound
#print axioms KoalaAt2428Gate49.receipt
