import ProximityPrize.SubmissionLower.KoalaGateSharedData
import ProximityPrize.SubmissionLower.KoalaGateChunkSums
import ProximityPrize.SubmissionLower.KoalaSplitGateWords

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000

set_option linter.defProp false

namespace KoalaAt2428Gate45
open KoalaGateSharedData
open FadicGate KoalaGateCheck
open KoalaWeightedRate (Envelope)
open KoalaFarBridge (rowCheck plainCheck)

def envelope : Envelope :=
  ⟨132,56,2,135,56,3432,4435,⟨4096359470,15552039010,148427958431⟩,1670026153359⟩
abbrev split:ℕ:=48
abbrev unit:ℕ:=1919966363520
abbrev terminal:ℕ:=65
abbrev gate:=KoalaSplitRow.rate envelope split unit

private def boxesTape : List (List Entry) := [
  b05p,b04y,b044,b038,b036,b025,b011,b00x,
  bzy,byu,byp,bxj,bvv,bvw,bua,bub,
  bsy,bsz,bs1,brz,br0,bqx,bq0,bot,
  bne,blp,bk5,bie,bifAtom,bfj,bfl,bbe,
  b6y.take 22,b7i.take 22,b7x.take 22,b87.take 22,b8k.take 22,b8t.take 22,b95.take 22,b9b.take 22,
  b9n.take 22,b9t.take 22,ba6.take 22,bac.take 22,bam.take 22]
def boxes (r : ℕ) : List FadicGate.Entry :=
  if r < 20 then [] else boxesTape.getD (r-20) []

def plain : ℕ → ℕ × ℕ × ℕ
  | _ => (0,0,0)

private def powersTape : List String := [
  "","","","","","","","",
  "","","","","","","","",
  "","","","","!#","!#%","!#%(","!#%)",
  z3p,"!#%(+/","!#$(,/","!#%',05","!#$'*06:","!#$'*176","!#$&+-27C","!#$'+-18DC",
  "!#$').29>D","!#$&).3:9FD","!#$&*/3;:GF","!#$&*,46;IGD","!#$&(,04<CIG","!#$&),/4==JIO","!#$&)-05==KJH","!#$%)-06>=MKJ]",
  "!#$&(+169>GMKU","!#$&(+176?AOMNi","!##%(+.37@?POLci","!#$%(+.27A@RPO[li","!##%',.28BAKRPSoli","!##%'*.28=BFSRNholi","!##%'*/398CBTSRaqoli","!##%(*/3:9DCUTSYtqol",
  "!!#%'*,46:DDPUTQmtqok","!!#%'+-04:EDJWUTfvtqo","!!#%')-04;AEDYWU_yvtqk","!!#%')-04;<FEZYWWryvtr","!!#%&)-05<;GFTZYWk|ywv","!!#%&)-15=<HGO]ZYd~!~|yv","!!#$'*+169=IHI^^_^w~#!~##v","!!#$'(+166=DII`__Yq~#$~##v",
  "!!#$&),.36>@JLZc_Yj~#,~##v","!!#$&),.27?>KLUc_Y[|~##v","!!#$&),.27?@NLMc_YUn~##v","!!#$&),/28B@NLIc_YU`~##v","!!#$&(*/39=@HLIZ_YUQrv","!!#$&(+/498@BLIQ_YUQdv","!!#$&(+0498@?LIH_YUQUv","!!#$&(+-458@?LIG_YUQLh"]

def powers (r : ℕ) : List ℕ :=
  if r=0 then [] else KoalaSplitGateWords.powers (powersTape.getD (r-1) "")

def plainPowers : ℕ → List ℕ
  | _ => []

def tailPowers : List ℕ := KoalaSplitGateWords.powers "!!#$&)+-038@?LIGUZUQLZmcYOE<2("

def priced (r:ℕ):Bool:=rowCheck gate r (boxes r) (powers r) (plain r) (plainPowers r)
private theorem priced_list : (List.range 64).all (fun i => priced (i+1)) = true := by decide +kernel

theorem prices {r : ℕ} (hr : 0 < r) (hR : r < terminal) : priced r = true :=
  price hr hR priced_list

theorem tail:plainCheck gate terminal (4012,1650,550) tailPowers=true:=by decide +kernel

private abbrev Chunk (i n v : ℕ) := lossChunk 24 envelope plain boxes i n = v
private theorem checkPart (i n v : ℕ) (ok : Chunk i n v := by decide +kernel) : Chunk i n v := ok
private def part0 := checkPart 0 6 0x2384dc4cc14
private def part1 := checkPart 6 6 0x2384dc4cc14
private def part2 := checkPart 12 6 0x2384dc4cc14
private def part3 := checkPart 18 6 0x234649b0de2
private def part4 := checkPart 24 6 0x226e2b1573f
private def part5 := checkPart 30 6 0x20dbe50e08a
private def part6 := checkPart 36 6 0x1e3f9778ad4
private def part7 := checkPart 42 6 0x19f9cc6f16c
private def part8 := checkPart 48 6 0x13c5246e3c7
private def part9 := checkPart 54 6 0xc76c2a3846
private def part10 := checkPart 60 4 0x4f05812535

theorem loss_bound (N : ℕ) : Bound envelope terminal plain boxes 20788868310889 N :=
  loss_of_chunks 24 envelope terminal plain boxes 20788868310889 N (by decide) (by decide)
    (LossSum.empty _ _ _ _
      |>.append 6 0x2384dc4cc14 part0 |>.append 6 0x2384dc4cc14 part1 |>.append 6 0x2384dc4cc14 part2 |>.append 6 0x234649b0de2 part3
      |>.append 6 0x226e2b1573f part4 |>.append 6 0x20dbe50e08a part5 |>.append 6 0x1e3f9778ad4 part6 |>.append 6 0x19f9cc6f16c part7
      |>.append 6 0x13c5246e3c7 part8 |>.append 6 0xc76c2a3846 part9 |>.append 4 0x4f05812535 part10)

def receipt : KoalaSplitProof.Receipt envelope split unit :=
  ⟨terminal, plain, boxes, powers, plainPowers, tailPowers, 20788868310889,
    by decide,by decide,loss_bound,fun _ h h' => prices h h', tail⟩

end KoalaAt2428Gate45

#print axioms KoalaAt2428Gate45.loss_bound
#print axioms KoalaAt2428Gate45.receipt
