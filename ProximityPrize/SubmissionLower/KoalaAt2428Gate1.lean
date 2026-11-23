import ProximityPrize.SubmissionLower.KoalaGateSharedData
import ProximityPrize.SubmissionLower.KoalaGateChunkSums
import ProximityPrize.SubmissionLower.KoalaSplitGateWords

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000

set_option linter.defProp false

namespace KoalaAt2428Gate1
open KoalaGateSharedData
open FadicGate KoalaGateCheck
open KoalaWeightedRate (Envelope)
open KoalaFarBridge (rowCheck plainCheck)

def envelope : Envelope :=
  ⟨101,56,9,110,56,2626,4260,⟨10165236311,40132182567,11654179719⟩,3346686505300⟩
abbrev split:ℕ:=24
abbrev unit:ℕ:=1920000000000
abbrev terminal:ℕ:=60
abbrev gate:=KoalaSplitRow.rate envelope split unit

private def boxesTape : List (List Entry) := [
  b05m,b04w,b041,b034,b024,b00x,b00z,bzw,
  byp,byq,byr,bxd,bvu,bub,bud,bsz,
  bt1,brz,bs0,bqx,bqw,bps,bpt,bpr,
  bok,bn6,blm,bk4,bih,bfk,bfo,bfn,
  b7z.take 21,b5r.take 21,b5s.take 21,b24.take 21,b2b.take 21,b2j.take 21]
def boxes (r : ℕ) : List FadicGate.Entry :=
  if r < 22 then [] else boxesTape.getD (r-22) []

def plain : ℕ → ℕ × ℕ × ℕ
  | _ => (0,0,0)

private def powersTape : List String := [
  "","","","","","","","",
  "","","","","","","","",
  "","","","","","","!#","!#$",
  "!!$'","!!$'*","!!$'+.","!!$&+/","!!$&)/6","!!$&)066","!!#%),16","!!#&*,07",
  "!!#&(,18>","!!#%(-198F","!!#%(-2:9HF","!!#%(*25:IH","!!#%'+.2;CIH","!!#%'+.3;<KI","!!#%'+.3<;LKM","!!#$'+/4=<NLJ",
  "!!#$&)/48=GNL]","!!#$')/54>AONS","!!#$'*,15?>POMk","!!#$'*,05??RPOc","!!#$&*,06@?KRPY","!!#$&(-06;@ESRPq","!!#$&(-176A@USRh}","!!#$&(-187BAVUS_~#!}",
  "!!!$%)*138CBPVUVw~#!}","!!!$%)+.18DCIXVTn~#&~#!}","!!!$%'+.29>DCYXVe~#(~#&~#!}","!!!#&'+.299DDZYX[}~#(~#&~#!","!!!#%(+.3:9EDTZYVt~#+~#(~#%","!!!#%(+.3::FEM]ZYk~#.~#+~#&","!!!#%()/36:GFG^]Y`~#%~#.~#(","!!!#%')/43;BGF`]YUw~#0~#(",
  "!!!#%'*,04;<HFW^YUg~#1~#(","!!!#%'*,/4<;HFO^YUV~!~~#(","!!!#%'*,/4<;IFF^YUQn~#("]
def powers (r : ℕ) : List ℕ :=
  if r=0 then [] else KoalaSplitGateWords.powers (powersTape.getD (r-1) "")

def plainPowers : ℕ → List ℕ
  | _ => []

def tailPowers:List ℕ:=KoalaSplitGateWords.powers "!!!#%'+-05><KIGc`[Wm~#8~#/~#&zqg^TK~#^"

def priced (r:ℕ):Bool:=rowCheck gate r (boxes r) (powers r) (plain r) (plainPowers r)
private theorem priced_list : (List.range 59).all (fun i => priced (i+1)) = true := by decide +kernel

theorem prices {r : ℕ} (hr : 0 < r) (hR : r < terminal) : priced r = true :=
  price hr hR priced_list

theorem tail:plainCheck gate terminal (4012,1650,550) tailPowers=true:=by decide +kernel

private abbrev Chunk (i n v : ℕ) := lossChunk 48 envelope plain boxes i n = v
private theorem checkPart (i n v : ℕ) (ok : Chunk i n v := by decide +kernel) : Chunk i n v := ok
private def part0 := checkPart 0 6 0x2384dc4cc14
private def part1 := checkPart 6 6 0x2384dc4cc14
private def part2 := checkPart 12 6 0x2384dc4cc14
private def part3 := checkPart 18 6 0x23686432c96
private def part4 := checkPart 24 6 0x229a1159b6e
private def part5 := checkPart 30 6 0x213c5d0414a
private def part6 := checkPart 36 6 0x1ee05e9bf77
private def part7 := checkPart 42 6 0x1b3ae924961
private def part8 := checkPart 48 6 0x15a4a1ce36c
private def part9 := checkPart 54 5 0xd089772856

theorem loss_bound (N : ℕ) : Bound envelope terminal plain boxes 20793522618916 N :=
  loss_of_chunks 48 envelope terminal plain boxes 20793522618916 N (by decide) (by decide)
    (LossSum.empty _ _ _ _
      |>.append 6 0x2384dc4cc14 part0 |>.append 6 0x2384dc4cc14 part1 |>.append 6 0x2384dc4cc14 part2 |>.append 6 0x23686432c96 part3
      |>.append 6 0x229a1159b6e part4 |>.append 6 0x213c5d0414a part5 |>.append 6 0x1ee05e9bf77 part6 |>.append 6 0x1b3ae924961 part7
      |>.append 6 0x15a4a1ce36c part8 |>.append 5 0xd089772856 part9)

def receipt : KoalaSplitProof.Receipt envelope split unit :=
  ⟨terminal, plain, boxes, powers, plainPowers, tailPowers, 20793522618916,
    by decide,by decide,loss_bound,fun _ h h' => prices h h', tail⟩

end KoalaAt2428Gate1

#print axioms KoalaAt2428Gate1.loss_bound
#print axioms KoalaAt2428Gate1.receipt
