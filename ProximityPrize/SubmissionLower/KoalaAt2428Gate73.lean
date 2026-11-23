import ProximityPrize.SubmissionLower.KoalaGateSharedData
import ProximityPrize.SubmissionLower.KoalaGateChunkSums
import ProximityPrize.SubmissionLower.KoalaSplitGateWords

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000

set_option linter.defProp false

namespace KoalaAt2428Gate73
open KoalaGateSharedData
open FadicGate KoalaGateCheck
open KoalaWeightedRate (Envelope)
open KoalaFarBridge (rowCheck plainCheck)

def envelope : Envelope :=
  ⟨112,55,8,115,55,2912,4365,⟨9595842248,42270520240,9771797913⟩,3401881460387⟩
abbrev split:ℕ:=48
abbrev unit:ℕ:=1919968056960
abbrev terminal:ℕ:=60
abbrev gate:=KoalaSplitRow.rate envelope split unit

private def boxesTape : List (List Entry) := [
  b05m,b04w,b041,b034,b039,b026,b00z,b012,
  b003,byq,byr,bxd,bvu,bub,bud,bsz,
  bt1,brz,bs0,bqx,bqw,bqy,bpt,bpr,
  bok,bn6,blm,bk4,bih,bik,bfo,bfn,
  bfp,bfq,bfr,bfs,bft,b5h.take 21]
def boxes (r : ℕ) : List FadicGate.Entry :=
  if r < 22 then [] else boxesTape.getD (r-22) []

def plain : ℕ → ℕ × ℕ × ℕ
  | _ => (0,0,0)

private def powersTape : List String := [
  "","","","","","","","",
  "","","","","","","","",
  "","","","","","","!#","!#%",
  "!#%(","!#%(","!#$(,","!#%'-0",z5V,"!#$'*29","!#$'+-49","!#$'+.2:",
  "!#$').3:B","!#$&)/3;;I","!#$&*/4<;KI","!#$&*,57<MK","!#$&(,05=FMK","!#$&)-05>@NM","!#$&)-06?>PNR","!#$%)-16@?QPN",
  "!#$&(+17;@KQPb","!#$&(+287AESQY","!##%(+.38BATSP","!#$%(,.28CBVTSi","!##%',.29DCPVT`","!##%'*/39?DIWVVw","!##%(*/3:9EDYWVn~#&","!##%(*/4;:EE[YWf~#)~#&",
  "!!#%'*-46;FET[Y]}~#)~#&","!!#%'+-14;GFN][Yu~#,~#)~#&","!!#%')-05<BGG_][l~#/~#,~#)","!!#%')-05<=HG`_]c~#'~#/~#,~#)","!!#%&)-15=<IHY`_[{~#3~#/~#,","!!#%&*.16>=JIRb`^r~#5~#3~#/","!!#$'*+169>KJLcb`i~#-~#5~#1","!!#$'(,276>FKJec`[~#$~#8~#1",
  "!!#$&),.37?ALK^d`[q~#;~#1","!!#$&),.27??MKUd`[`~#+~#1","!!#$&),/27@?MKLd`[Vw~#1"]

def powers (r : ℕ) : List ℕ :=
  if r=0 then [] else KoalaSplitGateWords.powers (powersTape.getD (r-1) "")

def plainPowers : ℕ → List ℕ
  | _ => []

def tailPowers : List ℕ := KoalaSplitGateWords.powers "!!#%'*-039A@OLJgc_Zp~#<~#2~#({qg]RH~#!~%/"

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
private def part3 := checkPart 18 6 0x2368247da87
private def part4 := checkPart 24 6 0x22a7b4913a0
private def part5 := checkPart 30 6 0x2136c5ab70a
private def part6 := checkPart 36 6 0x1ed4b49fe0d
private def part7 := checkPart 42 6 0x1b29c50466d
private def part8 := checkPart 48 6 0x15850545d9f
private def part9 := checkPart 54 5 0xcd20b3ee81

theorem loss_bound (N : ℕ) : Bound envelope terminal plain boxes 20764755270151 N :=
  loss_of_chunks 48 envelope terminal plain boxes 20764755270151 N (by decide) (by decide)
    (LossSum.empty _ _ _ _
      |>.append 6 0x2384dc4cc14 part0 |>.append 6 0x2384dc4cc14 part1 |>.append 6 0x2384dc4cc14 part2 |>.append 6 0x2368247da87 part3
      |>.append 6 0x22a7b4913a0 part4 |>.append 6 0x2136c5ab70a part5 |>.append 6 0x1ed4b49fe0d part6 |>.append 6 0x1b29c50466d part7
      |>.append 6 0x15850545d9f part8 |>.append 5 0xcd20b3ee81 part9)

def receipt : KoalaSplitProof.Receipt envelope split unit :=
  ⟨terminal, plain, boxes, powers, plainPowers, tailPowers, 20764755270151,
    by decide,by decide,loss_bound,fun _ h h' => prices h h', tail⟩

end KoalaAt2428Gate73

#print axioms KoalaAt2428Gate73.loss_bound
#print axioms KoalaAt2428Gate73.receipt
