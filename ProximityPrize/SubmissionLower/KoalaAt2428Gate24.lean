import ProximityPrize.SubmissionLower.KoalaGateSharedData
import ProximityPrize.SubmissionLower.KoalaGateChunkSums
import ProximityPrize.SubmissionLower.KoalaSplitGateWords

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000

set_option linter.defProp false

namespace KoalaAt2428Gate24
open KoalaGateSharedData
open FadicGate KoalaGateCheck
open KoalaWeightedRate (Envelope)
open KoalaFarBridge (rowCheck plainCheck)

def envelope : Envelope :=
  ⟨136,56,4,137,56,3536,4437,⟨8018654965,35575036038,81902217008⟩,3467427287245⟩
abbrev split:ℕ:=48
abbrev unit:ℕ:=1919967386880
abbrev terminal:ℕ:=71
abbrev gate:=KoalaSplitRow.rate envelope split unit

private def boxesTape : List (List Entry) := [
  b05l,b04u,b03z,b043,b035,b023,b00w,b00y,
  bzv,bzx,byt,bxb,bvt,bvs,bvv,bu9,
  bua,bt0,bsy,bs2,bs1,br1,bpx,bor,
  bn9,blk,bln,bk2,big,bie,bfm,bfj,
  bbb,bbc,bc4,b7e,b7v,b85,b8j,b8q,
  b93,b99,b9m,b9r,ba4,baa,bak,baq,
  b65,b62,b67,b6a,[]]
def boxes (r : ℕ) : List FadicGate.Entry :=
  if r < 18 then [] else boxesTape.getD (r-18) []

def plain : ℕ → ℕ × ℕ × ℕ
  | 70 => (3914, 1630, 408)
  | _ => (0,0,0)

private def powersTape : List String := [
  "","","","","","","","",
  "","","","","","","","",
  "","","!#","!#&","!#&","!#&)",z3O,z2Q,
  "!#%(-7","!#%)-37","!#%)-28","!#%(.2:H",z6Z,"!#%(,4<<JK","!#$',07<KJ","!#$',/4=MK",
  "!#$'*05>GMR","!#$'*06?AOM","!#$'+16@?QOb","!#$'+-7;@SQY","!#$&).37AMSQq","!#$&*.28BGTSi","!#$&*.28CBVTa~#!","!#$&*/39DCXVYx~#!",
  "!#$&),3:?DRXVp~#&~#!","!#$&),4;:ELZXi~#)~#&~#!","!#$&)-07;FF]Zb~#!~#)~#&~#!","!#$&)-04;GF^]Zx~#-~#)~#&","!#$&(-05<IGW^]p~#1~#-~#)~#&","!#$%(+15=DIR`^h~#)~#1~#-~#)}","!##%(+16=?JLb`a~#!~#4~#1~#-~#)","!##%(+16>=KJdb`w~#8~#4~#1~#-}",
  "!!#%',.7:>LK^dbp~#0~#8~#4~#1~#+","!!#%(,.37?MLWfdi~#)~#;~#8~#4~#1}","!!#%(*.27?HMQgfd~#!~#?~#;~#8~#4~#*","!!#%(*/28@CNMigfw~#8~#?~#;~#6~#1","!!#%'*/38A@ONcigo~#0~#C~#>~#:~#4~#'","!!#%'+/39BAPO]kig~#(~#F~#B~#<~#4~#'","!!#%'+-39=BQPWmlj|~#>~#E~#@~#4~#'","!!#%')-4:9BLQPomjp~#4~#H~#@~#4~#'",
  "!!#%')-16:CHRRioje~#(~#N~#@~#4~#'","!!#$'*-04:DCSRbojet~#=~#@~#4~#'","!!#%'*.05;DDURWojec~#,~#@~#4~#'","!!#%'*.15;FDUROoje_x~#@~#4~#'","!!#$&),15<ADNROfje_g~#0~#4~#'","!!#$&),16<<DHRO]je_Y|~#4~#'","!!#$&),26<;DBRORje_Yk~#4~#'","!!#$&),/68;DBROLje_YY~##~#'",
  "!!#$&),.25;DBROLae_YTo~#'","!!#$&(,.15;DBKOLVe_YT^~#'","!!#$&(*.15;?BEOLMe_YTOs","!!#$&(*.15;:B@OLIe_YTOb","!!#$&(*.15;:B@OLIZ_YTOP",""]

def powers (r : ℕ) : List ℕ :=
  if r=0 then [] else KoalaSplitGateWords.powers (powersTape.getD (r-1) "")

private def plainPowers : ℕ → List ℕ
  | 70 => [0, 0, 1, 2, 3, 6, 8, 12, 15, 19, 24, 23, 31, 30, 44, 41, 38, 45, 58, 53, 48, 43, 37, 62, 66, 52, 40, 27, 14]
  | _ => []

def tailPowers : List ℕ := KoalaSplitGateWords.powers "!!#$&'*,157:B@HLIH`YTOJTj]OB5("

def priced (r:ℕ):Bool:=rowCheck gate r (boxes r) (powers r) (plain r) (plainPowers r)
private theorem priced_list : (List.range 70).all (fun i => priced (i+1)) = true := by decide +kernel

theorem prices {r : ℕ} (hr : 0 < r) (hR : r < terminal) : priced r = true :=
  price hr hR priced_list

theorem tail:plainCheck gate terminal (4012,1650,550) tailPowers=true:=by decide +kernel

private abbrev Chunk (i n v : ℕ) := lossChunk 16 envelope plain boxes i n = v
private theorem checkPart (i n v : ℕ) (ok : Chunk i n v := by decide +kernel) : Chunk i n v := ok
private def part0 := checkPart 0 6 0x2384dc4cc14
private def part1 := checkPart 6 6 0x2384dc4cc14
private def part2 := checkPart 12 6 0x23823c933d9
private def part3 := checkPart 18 6 0x232abbdad9f
private def part4 := checkPart 24 6 0x2252abb492d
private def part5 := checkPart 30 6 0x20c0cc57280
private def part6 := checkPart 36 6 0x1e08fd8c2e1
private def part7 := checkPart 42 6 0x19a9ce35de9
private def part8 := checkPart 48 6 0x13558932b6e
private def part9 := checkPart 54 6 0xbcdb1e644a
private def part10 := checkPart 60 6 0x5cf66de895
private def part11 := checkPart 66 4 0x1df8ba2b71

theorem loss_bound (N : ℕ) : Bound envelope terminal plain boxes 20843243960789 N :=
  loss_of_chunks 16 envelope terminal plain boxes 20843243960789 N (by decide) (by decide)
    (LossSum.empty _ _ _ _
      |>.append 6 0x2384dc4cc14 part0 |>.append 6 0x2384dc4cc14 part1 |>.append 6 0x23823c933d9 part2 |>.append 6 0x232abbdad9f part3
      |>.append 6 0x2252abb492d part4 |>.append 6 0x20c0cc57280 part5 |>.append 6 0x1e08fd8c2e1 part6 |>.append 6 0x19a9ce35de9 part7
      |>.append 6 0x13558932b6e part8 |>.append 6 0xbcdb1e644a part9 |>.append 6 0x5cf66de895 part10 |>.append 4 0x1df8ba2b71 part11)

def receipt : KoalaSplitProof.Receipt envelope split unit :=
  ⟨terminal, plain, boxes, powers, plainPowers, tailPowers, 20843243960789,
    by decide,by decide,loss_bound,fun _ h h' => prices h h', tail⟩

end KoalaAt2428Gate24

#print axioms KoalaAt2428Gate24.loss_bound
#print axioms KoalaAt2428Gate24.receipt
