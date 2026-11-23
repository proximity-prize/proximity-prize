import ProximityPrize.SubmissionLower.KoalaGateSharedData
import ProximityPrize.SubmissionLower.KoalaGateChunkSums
import ProximityPrize.SubmissionLower.KoalaSplitGateWords

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000

set_option linter.defProp false

namespace KoalaAt2428Gate66
open KoalaGateSharedData
open FadicGate KoalaGateCheck
open KoalaWeightedRate (Envelope)
open KoalaFarBridge (rowCheck plainCheck)

def envelope : Envelope :=
  ⟨136,50,2,136,50,3536,4436,⟨2224968752,9776983729,144741849974⟩,904630866747⟩
abbrev split:ℕ:=48
abbrev unit:ℕ:=1919966263680
abbrev terminal:ℕ:=55
abbrev gate:=KoalaSplitRow.rate envelope split unit

private def boxesTape : List (List Entry) := [
  b05s,b052,b047,b03b,b029,b02a,b015,b001,
  b002,byw,bxk,bvx,bvy,bw1,bue,bt4,
  bs5,br4,br5,bpv,bq1,bop,bov,bn7,
  bnf,b7f.take 17,b7w.take 18]
def boxes (r : ℕ) : List FadicGate.Entry :=
  if r < 28 then [] else boxesTape.getD (r-28) []

def plain : ℕ → ℕ × ℕ × ℕ
  | _ => (0,0,0)

private def powersTape : List String := [
  "","","","","","","","",
  "","","","","","","","",
  "","","","","","","","",
  "","","","","!#","!#$","!#$&","!#$&)",
  "!#$&(","!#$%(,","!#$&(-0","!#$&)*1","!#$%'*-1","!#$%(+-18","!##%(+.288",z6I,
  "!##%').349","!##%')/33:9","!##%'*,/3;:G","!##%'*,/4;;HG",z50,"!##%'),057<<IH","!##%')-055=<KIH","!##%')-065==KKI",
  "!!#$&)+116>=EKKH","!!#$&)+-16?>?MKJ","!!#$&(+-17:?>NMKJ",z6e,z6f,"!!#$&(,.287A@CPPON"]

def powers (r : ℕ) : List ℕ :=
  if r=0 then [] else KoalaSplitGateWords.powers (powersTape.getD (r-1) "")

def plainPowers : ℕ → List ℕ
  | _ => []

def tailPowers : List ℕ := KoalaSplitGateWords.powers "!!#%'*,27:>KII`]Y[|~#%{tmf_Wo~#8~#>~#&"

def priced (r:ℕ):Bool:=rowCheck gate r (boxes r) (powers r) (plain r) (plainPowers r)
private theorem priced_list : (List.range 54).all (fun i => priced (i+1)) = true := by decide +kernel

theorem prices {r : ℕ} (hr : 0 < r) (hR : r < terminal) : priced r = true :=
  price hr hR priced_list

theorem tail:plainCheck gate terminal (4012,1650,550) tailPowers=true:=by decide +kernel

private abbrev Chunk (i n v : ℕ) := lossChunk 128 envelope plain boxes i n = v
private theorem checkPart (i n v : ℕ) (ok : Chunk i n v := by decide +kernel) : Chunk i n v := ok
private def part0 := checkPart 0 6 0x2384dc4cc14
private def part1 := checkPart 6 6 0x2384dc4cc14
private def part2 := checkPart 12 6 0x2384dc4cc14
private def part3 := checkPart 18 6 0x2384dc4cc14
private def part4 := checkPart 24 6 0x23564d78c7b
private def part5 := checkPart 30 6 0x2227afd823c
private def part6 := checkPart 36 6 0x203e157112b
private def part7 := checkPart 42 6 0x1d33f19ffec
private def part8 := checkPart 48 6 0x18ec88db764

theorem loss_bound (N : ℕ) : Bound envelope terminal plain boxes 20474107463554 N :=
  loss_of_chunks 128 envelope terminal plain boxes 20474107463554 N (by decide) (by decide)
    (LossSum.empty _ _ _ _
      |>.append 6 0x2384dc4cc14 part0 |>.append 6 0x2384dc4cc14 part1 |>.append 6 0x2384dc4cc14 part2 |>.append 6 0x2384dc4cc14 part3
      |>.append 6 0x23564d78c7b part4 |>.append 6 0x2227afd823c part5 |>.append 6 0x203e157112b part6 |>.append 6 0x1d33f19ffec part7
      |>.append 6 0x18ec88db764 part8)

def receipt : KoalaSplitProof.Receipt envelope split unit :=
  ⟨terminal, plain, boxes, powers, plainPowers, tailPowers, 20474107463554,
    by decide,by decide,loss_bound,fun _ h h' => prices h h', tail⟩

end KoalaAt2428Gate66

#print axioms KoalaAt2428Gate66.loss_bound
#print axioms KoalaAt2428Gate66.receipt
