import ProximityPrize.SubmissionLower.KoalaGateSharedData
import ProximityPrize.SubmissionLower.KoalaGateChunkSums
import ProximityPrize.SubmissionLower.KoalaSplitGateWords

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000

set_option linter.defProp false

namespace KoalaAt2428Gate69
open KoalaGateSharedData
open FadicGate KoalaGateCheck
open KoalaWeightedRate (Envelope)
open KoalaFarBridge (rowCheck plainCheck)

def envelope : Envelope :=
  ⟨133,50,2,135,50,3458,4435,⟨2242560479,9693005481,143825345143⟩,898876379833⟩
abbrev split:ℕ:=48
abbrev unit:ℕ:=1919966275200
abbrev terminal:ℕ:=55
abbrev gate:=KoalaSplitRow.rate envelope split unit

private def boxesTape : List (List Entry) := [
  b05s,b052,b047,b03b,b029,b02a,b015,b001,
  b002,byw,bxk,bvx,bvy,bn5.take 11,bue,bt4,
  bs5,br4,br5,bpv,bq1,bop,bov,bn7,
  bnf,bnh,b4u.take 18]
def boxes (r : ℕ) : List FadicGate.Entry :=
  if r < 28 then [] else boxesTape.getD (r-28) []

def plain : ℕ → ℕ × ℕ × ℕ
  | _ => (0,0,0)

private def powersTape : List String := [
  "","","","","","","","",
  "","","","","","","","",
  "","","","","","","","",
  "","","","","!#","!#$","!#$&","!#$&)",
  "!#$&(","!#$%(,","!#$&(,0","!#$&(*1","!#$%'*-1","!#$%'+-18","!##%(+-288",z6I,
  "!##%').349>","!##%').33:9","!##%'*,/3::G","!##%'*,/3;:HG",z50,"!##%'),047<<IH","!##%')-054=<JIH","!##%')-055==KJI",
  "!!#$&)+115>=EKJH","!!#$&)+-16?>?LKJ","!!#$&(+-16:?>NLKI","!!#$&(+.176??ONLI","!!#$&(+.277@?IONL",z6c]

def powers (r : ℕ) : List ℕ :=
  if r=0 then [] else KoalaSplitGateWords.powers (powersTape.getD (r-1) "")

def plainPowers : ℕ → List ℕ
  | _ => []

def tailPowers : List ℕ := KoalaSplitGateWords.powers "!!#%'*,27:>KII`]XZ|~#%{tmf_Wo~#8~#>~#%k"

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
private def part4 := checkPart 24 6 0x2356b249cab
private def part5 := checkPart 30 6 0x222aaa0a165
private def part6 := checkPart 36 6 0x203e74c10a7
private def part7 := checkPart 42 6 0x1d41fbca1fc
private def part8 := checkPart 48 6 0x190461d89a4

theorem loss_bound (N : ℕ) : Bound envelope terminal plain boxes 20485282638503 N :=
  loss_of_chunks 128 envelope terminal plain boxes 20485282638503 N (by decide) (by decide)
    (LossSum.empty _ _ _ _
      |>.append 6 0x2384dc4cc14 part0 |>.append 6 0x2384dc4cc14 part1 |>.append 6 0x2384dc4cc14 part2 |>.append 6 0x2384dc4cc14 part3
      |>.append 6 0x2356b249cab part4 |>.append 6 0x222aaa0a165 part5 |>.append 6 0x203e74c10a7 part6 |>.append 6 0x1d41fbca1fc part7
      |>.append 6 0x190461d89a4 part8)

def receipt : KoalaSplitProof.Receipt envelope split unit :=
  ⟨terminal, plain, boxes, powers, plainPowers, tailPowers, 20485282638503,
    by decide,by decide,loss_bound,fun _ h h' => prices h h', tail⟩

end KoalaAt2428Gate69

#print axioms KoalaAt2428Gate69.loss_bound
#print axioms KoalaAt2428Gate69.receipt
