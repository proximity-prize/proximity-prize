import ProximityPrize.SubmissionLower.KoalaGateSharedData
import ProximityPrize.SubmissionLower.KoalaGateChunkSums
import ProximityPrize.SubmissionLower.KoalaSplitGateWords

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000

set_option linter.defProp false

namespace KoalaAt2428Gate2
open KoalaGateSharedData
open FadicGate KoalaGateCheck
open KoalaWeightedRate (Envelope)
open KoalaFarBridge (rowCheck plainCheck)

def envelope : Envelope :=
  ⟨109,56,7,112,56,2834,4312,⟨10188047166,41842048783,10434318772⟩,3472952724807⟩
abbrev split:ℕ:=24
abbrev unit:ℕ:=1919998521600
abbrev terminal:ℕ:=61
abbrev gate:=KoalaSplitRow.rate envelope split unit

private def boxesTape : List (List Entry) := [
  b05n,b04v,b042,b041,b034,b024,b00x,b00z,
  bzw,byp,byq,byr,bxd,bvu,bub,bud,
  bsz,bt1,brz,bs0,bqx,bqw,bps,bpt,
  bpr,bok,blq,bk7,bii,bfl,bfk,bfo,
  bbg,bbh,bbl,bbn,bbp,bbr,bbt,bbu]
def boxes (r : ℕ) : List FadicGate.Entry :=
  if r < 21 then [] else boxesTape.getD (r-21) []

def plain : ℕ → ℕ × ℕ × ℕ
  | _ => (0,0,0)

private def powersTape : List String := [
  "","","","","","","","",
  "","","","","","","","",
  "","","","","","!#","!#$","!#$",
  "!!$'","!!$'*","!!$'+.","!!$&+/","!!$&)/6","!!$&)076","!!#&),27","!!#&*,08",
  "!!#&(-19?","!!#%(-299G","!!#%(-2:9IG","!!#%)+35:JI","!!#%'+.3;DJI","!!#%'+.3<=LJ","!!#%'+/4=<MLO","!!#$(,/4>=OMK",
  "!!#$&)/58>HOM_","!!#$')055>BPOU","!!#$'*,15?>RPNn","!!#$'*,06@?SRPe","!!#$&*-06A@MSR[","!!#$&(-17<AFUSSt","!!#$&(-177BAVUSk~##}","!!#$&)-187CBWVUb~#&~##}",
  "!!!$%)+248DCQWVYz~#&~##}","!!!$%)+.29DDJYWVq~#)~#&~##}","!!!$&'+.29?DDZYWh~#,~#)~#&~##","!!!#&(+.3::ED]ZY_~##~#,~#)~#&","!!!#%(+.3::FEU]ZXw~#/~#,~#)~!~","!!!#%(,/3;:GFO^]Zn~#2~#/~#*~!~","!!!#%()/46;HGH`^[c~#)~#1~#+~!~","!!!#%'*/44;CHGa_[W{~#4~#+~!~",
  "!!!#%'*,04<=HGY`[Wk~#5~#+~!~","!!!#%'*,/4<;IGP`[WY~#$~#+~!~","!!!#%'*,05=<IGG`[WSq~#+~!~","!!!#%'*,05=<IGE`[WS`~#+~!~"]

def powers (r : ℕ) : List ℕ :=
  if r=0 then [] else KoalaSplitGateWords.powers (powersTape.getD (r-1) "")

def plainPowers : ℕ → List ℕ
  | _ => []

def tailPowers : List ℕ := KoalaSplitGateWords.powers "!!!#$&)-069=DIGY`[WZ~#'~#.~#$wndYPF<"

def priced (r:ℕ):Bool:=rowCheck gate r (boxes r) (powers r) (plain r) (plainPowers r)
private theorem priced_list : (List.range 60).all (fun i => priced (i+1)) = true := by decide +kernel

theorem prices {r : ℕ} (hr : 0 < r) (hR : r < terminal) : priced r = true :=
  price hr hR priced_list

theorem tail:plainCheck gate terminal (4012,1650,550) tailPowers=true:=by decide +kernel

private abbrev Chunk (i n v : ℕ) := lossChunk 32 envelope plain boxes i n = v
private theorem checkPart (i n v : ℕ) (ok : Chunk i n v := by decide +kernel) : Chunk i n v := ok
private def part0 := checkPart 0 6 0x2384dc4cc14
private def part1 := checkPart 6 6 0x2384dc4cc14
private def part2 := checkPart 12 6 0x2384dc4cc14
private def part3 := checkPart 18 6 0x235b0b45ebb
private def part4 := checkPart 24 6 0x228ce3be8c7
private def part5 := checkPart 30 6 0x211b55f4cac
private def part6 := checkPart 36 6 0x1e9ce24781f
private def part7 := checkPart 42 6 0x1aba657e9b2
private def part8 := checkPart 48 6 0x14c9da29d30
private def part9 := checkPart 54 6 0xddd44ec6eb

theorem loss_bound (N : ℕ) : Bound envelope terminal plain boxes 20723285081686 N :=
  loss_of_chunks 32 envelope terminal plain boxes 20723285081686 N (by decide) (by decide)
    (LossSum.empty _ _ _ _
      |>.append 6 0x2384dc4cc14 part0 |>.append 6 0x2384dc4cc14 part1 |>.append 6 0x2384dc4cc14 part2 |>.append 6 0x235b0b45ebb part3
      |>.append 6 0x228ce3be8c7 part4 |>.append 6 0x211b55f4cac part5 |>.append 6 0x1e9ce24781f part6 |>.append 6 0x1aba657e9b2 part7
      |>.append 6 0x14c9da29d30 part8 |>.append 6 0xddd44ec6eb part9)

def receipt : KoalaSplitProof.Receipt envelope split unit :=
  ⟨terminal, plain, boxes, powers, plainPowers, tailPowers, 20723285081686,
    by decide,by decide,loss_bound,fun _ h h' => prices h h', tail⟩

end KoalaAt2428Gate2

#print axioms KoalaAt2428Gate2.loss_bound
#print axioms KoalaAt2428Gate2.receipt
