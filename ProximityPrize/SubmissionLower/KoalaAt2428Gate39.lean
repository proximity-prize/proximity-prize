import ProximityPrize.SubmissionLower.KoalaAt2428Gate38
import ProximityPrize.SubmissionLower.KoalaGateSharedData
import ProximityPrize.SubmissionLower.KoalaGateChunkSums
import ProximityPrize.SubmissionLower.KoalaSplitGateWords

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000

set_option linter.defProp false

namespace KoalaAt2428Gate39
open KoalaGateSharedData
open FadicGate KoalaGateCheck
open KoalaWeightedRate (Envelope)
open KoalaFarBridge (rowCheck plainCheck)

def envelope : Envelope :=
  ⟨132,54,8,135,54,3432,4435,⟨8807271840,46203842566,29233425564⟩,3818219785381⟩
abbrev split:ℕ:=48
abbrev unit:ℕ:=1919967786240
abbrev terminal:ℕ:=67
abbrev gate:=KoalaSplitRow.rate envelope split unit

private def boxesTape : List (List Entry) := [
  b05k,b04t,b040,b03z,b033,b022,b010,b00w,
  bzz,bzv,bys,bxc,bxb,bvt,bvs,buc,
  bu9,bt2,bt0,bsy,br2,bpw,boq,bnc,
  bn5,bll,blk,bk3,bk2,big,bie,bfm,
  bfj,bbb,bbe,b5p,b59,b4u,b4w,b4y,
  b50,b51,b52,b53,b54,b55,b56,b57,
  b5k,b5n]
def boxes (r : ℕ) : List FadicGate.Entry :=
  if r < 17 then [] else boxesTape.getD (r-17) []

def plain : ℕ → ℕ × ℕ × ℕ
  | _ => (0,0,0)

private def powersTape : List String := [
  "","","","","","","","",
  "","","","","","","","",
  "","!#","!#&","!#&","!#&+",z4E,z4D,z2Q,
  "!#%(,7<",z3g,z46,"!#%(.29GF",z6Y,z6M,z48,"!#$',/4<MKY",
  "!#$'*05=GMQ","!#$'*05>@NMj","!#$'*06?>PNb",z5r,"!#$&)-27@LRPqy","!#$&).17AFTRi}y","!#$&*.28BAUT`~##}y","!#$&*.29CBWUWx~##}y",
  "!#$&(,39>CQWUp~#'~##}","!#$&),3:9DKYWh~#+~#'~##}","!#$%),06:ED[Y`~##~#+~#'~##","!#$&)-/4;FE][Yw~#.~#+~#'~!~","!#$&(-04;HFV][o~#2~#.~#+~#'","!#$%(+05<CHP_]g~#*~#2~#.~#+~!~","!##%(+05=>IJa_^~!~~#5~#2~#.~#+","!##%(+16==JIca_v~#9~#5~#2~#.~!~",
  "!!#%'+.69=KJ]can~#1~#9~#5~#2~#,","!!#%',.36>LKUecf~#)~#=~#9~#5~#2~!~","!!#%(*.17?GLOfec~!~~#@~#=~#9~#5~#,","!!#%(*.27?BMLhfeu~#8~#@~#=~#8~#4~!~","!!#%'*/27@?NMbhfm~#0~#D~#@~#<~#6~#)","!!#%'*/28A@ON[jhf~#(~#G~#D~#@~#6~#)","!!#%'+,38=APOUljh|~#?~#G~#B~#6~#)","!!#%')-398AKPOnlhm~#6~#J~#B~#6~#)",
  "!!#%&)-059BFQPgmhc~#'~#N~#B~#6~#)","!!#$')-049CBRP_mhcr~#=~#B~#6~#)","!!#$')-04:CCSPUmhc`~#,~#B~#6~#)","!!#$'*-04:DCSPMmhc^w~#B~#6~#)","!!#$&(+05;?CLPMdhc^e~#1~#6~#)","!!#$&)+15;:CEPMYhc^X|~#6~#)","!!#$&),15;:CAPMPhc^Xk~#6~#)","!!#$&),.57:CAPMKhc^XX~#$~#)",
  "!!#$&),.14:CAPMK_c^XSp~#)","!!#$&(,.04:CAIMKTc^XS^~#)"]

def powers (r : ℕ) : List ℕ :=
  if r=0 then [] else KoalaSplitGateWords.powers (powersTape.getD (r-1) "")

def plainPowers : ℕ → List ℕ
  | _ => []

def tailPowers : List ℕ := KoalaSplitGateWords.powers "!!#$&(*.04:>ACNKLe`ZUQz~#!sgZMA5)"

def priced (r:ℕ):Bool:=rowCheck gate r (boxes r) (powers r) (plain r) (plainPowers r)
private theorem priced_list : (List.range 66).all (fun i => priced (i+1)) = true := by decide +kernel

theorem prices {r : ℕ} (hr : 0 < r) (hR : r < terminal) : priced r = true :=
  price hr hR priced_list

theorem tail:plainCheck gate terminal (4012,1650,550) tailPowers=true:=by decide +kernel

private abbrev Chunk (i n v : ℕ) := lossChunk 12 envelope plain boxes i n = v
private theorem checkPart (i n v : ℕ) (ok : Chunk i n v := by decide +kernel) : Chunk i n v := ok
private def part0 := checkPart 0 6 0x2384dc4cc14
private def part1 := checkPart 6 6 0x2384dc4cc14
private def part2 := checkPart 12 6 0x237dfe50acc
private def part3 := checkPart 18 6 0x2323bf9cf03
private def part4 := checkPart 24 6 0x2252302d63a
private def part5 := checkPart 30 6 0x20cb57fb8cf
private def part6 := checkPart 36 6 0x1e13b6949f2
private def part7 := checkPart 42 6 0x19df7f8aa9d
private def part8 := checkPart 48 6 0x13ac7f371ae
private def part9 := checkPart 54 6 0xc2607fdf8b
private def part10 := checkPart 60 6 0x61cd4723ec

theorem loss_bound (N : ℕ) : Bound envelope terminal plain boxes 20799335918260 N :=
  loss_of_chunks 12 envelope terminal plain boxes 20799335918260 N (by decide) (by decide)
    (LossSum.empty _ _ _ _
      |>.append 6 0x2384dc4cc14 part0 |>.append 6 0x2384dc4cc14 part1 |>.append 6 0x237dfe50acc part2 |>.append 6 0x2323bf9cf03 part3
      |>.append 6 0x2252302d63a part4 |>.append 6 0x20cb57fb8cf part5 |>.append 6 0x1e13b6949f2 part6 |>.append 6 0x19df7f8aa9d part7
      |>.append 6 0x13ac7f371ae part8 |>.append 6 0xc2607fdf8b part9 |>.append 6 0x61cd4723ec part10)

def receipt : KoalaSplitProof.Receipt envelope split unit :=
  ⟨terminal, plain, boxes, powers, plainPowers, tailPowers, 20799335918260,
    by decide,by decide,loss_bound,fun _ h h' => prices h h', tail⟩

end KoalaAt2428Gate39

#print axioms KoalaAt2428Gate39.loss_bound
#print axioms KoalaAt2428Gate39.receipt
