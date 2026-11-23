import ProximityPrize.SubmissionLower.KoalaGateSharedData
import ProximityPrize.SubmissionLower.KoalaGateChunkSums
import ProximityPrize.SubmissionLower.KoalaSplitGateWords

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000

set_option linter.defProp false

namespace KoalaAt2428Gate32
open KoalaGateSharedData
open FadicGate KoalaGateCheck
open KoalaWeightedRate (Envelope)
open KoalaFarBridge (rowCheck plainCheck)

def envelope : Envelope :=
  ⟨136,55,4,137,55,3536,4437,⟨7651907098,34967768207,77417850428⟩,3323436459082⟩
abbrev split:ℕ:=48
abbrev unit:ℕ:=1919967221760
abbrev terminal:ℕ:=69
abbrev gate:=KoalaSplitRow.rate envelope split unit

private def boxesTape : List (List Entry) := [
  b05l,b04u,b03z,b043,b035,b023,b00w,b00y,
  bzv,bzx,byt,bxb,bvt,bvs,bvv,bu9,
  bua,bt0,bsy,bs2,bs1,br1,bpx,bor,
  bn9,blk,bln,bk2,bk5,bie,bfm,bfj,
  bbb,bbc,bbv,b4s,b4t,b4v,b4x,b4z,
  b4l,b4m,b4n,b4o,b4p,b4q,b4r,b58,
  b5m,b5l,b69]
def boxes (r : ℕ) : List FadicGate.Entry :=
  if r < 18 then [] else boxesTape.getD (r-18) []

def plain : ℕ → ℕ × ℕ × ℕ
  | _ => (0,0,0)

private def powersTape : List String := [
  "","","","","","","","",
  "","","","","","","","",
  "","","!#","!#&","!#&","!#&)",z3O,z2Q,
  z4a,z3g,"!#%)-18","!#%'.29F","!#$(+2:@F","!#%(+3;:HG","!#$',/6;JH","!#$',/4<KJ",
  "!#$'*/4=EKN","!#$&*05>?MK","!#$'*06?>OM^","!#$'+-6:?QOU","!#$&)-26@JQOl","!#$&).17ADRQd","!#$&*.28BATR[z","!#$&*.28CBVTTsz",
  "!#$&(,39>CPVTk~!~z","!#$&),3:9DJXVd~#$~!~z","!#$%),06:EDYX[z~#$~!~z","!#$&)-/4:FE[YXr~#(~#$~!~","!#$&(-04;GFU[Yj~#+~#(~#$~!~","!#$%(+05<BGO^[b~##~#+~#(~#$","!##%(+05<=HI`^[y~#/~#+~#(~#$","!##%(+15=<IHa`^q~#2~#/~#+~#(x",
  "!!#%'+.69=JIZa`i~#*~#2~#/~#+~#&","!!#%',.26>KJTcab~##~#5~#2~#/~#+x","!!#%'*.16>FKNecax~#9~#5~#2~#.~#%","!!#%(*.27?ALKfecp~#1~#9~#5~#0~#-","!!#%'*/27@?ML`feh~#)~#<~#8~#4~#1~#%","!!#%'*/28@@NMYhfd~!~~#?~#;~#8~#1~#%","!!#%'*,38<@ONTjhhv~#7~#>~#>~#1~#%","!!#%')-398AJOOljhl~#/~#B~#>~#1~#%",
  "!!#%&)-059BFPPfmhc~#$~#H~#>~#1~#%","!!#$')-049BBQP_mhcp~#9~#>~#1~#%","!!#$')-04:CCSPUmhc`~#(~#>~#1~#%","!!#$'*-04:ECSPNmhc^u~#>~#1~#%","!!#$&(+05;@CMPNdhc^d~#-~#1~#%","!!#$&),15;;CFPNZhc^Xy~#1~#%","!!#$&),15;:CAPNPhc^Xi~#1~#%","!!#$&),.57:CAPNKhc^XW~!~~#%",
  "!!#$&),.24:CAPNK_c^XSm~#%","!!#$&(,.14:CAJNKUc^XS]~#%","!!#$&(*.14:>ACNKKc^XSNr","!!#$&(*.14:9A@NKHc^XSNa"]

def powers (r : ℕ) : List ℕ :=
  if r=0 then [] else KoalaSplitGateWords.powers (powersTape.getD (r-1) "")

def plainPowers : ℕ → List ℕ
  | _ => []

def tailPowers : List ℕ := KoalaSplitGateWords.powers "!!#$&(*.14:9A@NKHY^XSNPwk^QE9-"

def priced (r:ℕ):Bool:=rowCheck gate r (boxes r) (powers r) (plain r) (plainPowers r)
private theorem priced_list : (List.range 68).all (fun i => priced (i+1)) = true := by decide +kernel

theorem prices {r : ℕ} (hr : 0 < r) (hR : r < terminal) : priced r = true :=
  price hr hR priced_list

theorem tail:plainCheck gate terminal (4012,1650,550) tailPowers=true:=by decide +kernel

private abbrev Chunk (i n v : ℕ) := lossChunk 16 envelope plain boxes i n = v
private theorem checkPart (i n v : ℕ) (ok : Chunk i n v := by decide +kernel) : Chunk i n v := ok
private def part0 := checkPart 0 6 0x2384dc4cc14
private def part1 := checkPart 6 6 0x2384dc4cc14
private def part2 := checkPart 12 6 0x238243c8f88
private def part3 := checkPart 18 6 0x232bbb4fb79
private def part4 := checkPart 24 6 0x225629f8ba4
private def part5 := checkPart 30 6 0x20c91331da1
private def part6 := checkPart 36 6 0x1e19af8395a
private def part7 := checkPart 42 6 0x19caa8d304d
private def part8 := checkPart 48 6 0x1385dd663e7
private def part9 := checkPart 54 6 0xbf15cc4093
private def part10 := checkPart 60 6 0x5e1025770e
private def part11 := checkPart 66 2 0x109f77ce6d

theorem loss_bound (N : ℕ) : Bound envelope terminal plain boxes 20829921550346 N :=
  loss_of_chunks 16 envelope terminal plain boxes 20829921550346 N (by decide) (by decide)
    (LossSum.empty _ _ _ _
      |>.append 6 0x2384dc4cc14 part0 |>.append 6 0x2384dc4cc14 part1 |>.append 6 0x238243c8f88 part2 |>.append 6 0x232bbb4fb79 part3
      |>.append 6 0x225629f8ba4 part4 |>.append 6 0x20c91331da1 part5 |>.append 6 0x1e19af8395a part6 |>.append 6 0x19caa8d304d part7
      |>.append 6 0x1385dd663e7 part8 |>.append 6 0xbf15cc4093 part9 |>.append 6 0x5e1025770e part10 |>.append 2 0x109f77ce6d part11)

def receipt : KoalaSplitProof.Receipt envelope split unit :=
  ⟨terminal, plain, boxes, powers, plainPowers, tailPowers, 20829921550346,
    by decide,by decide,loss_bound,fun _ h h' => prices h h', tail⟩

end KoalaAt2428Gate32

#print axioms KoalaAt2428Gate32.loss_bound
#print axioms KoalaAt2428Gate32.receipt
