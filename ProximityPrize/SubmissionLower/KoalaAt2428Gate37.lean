import ProximityPrize.SubmissionLower.KoalaAt2428Gate36
import ProximityPrize.SubmissionLower.KoalaGateSharedData
import ProximityPrize.SubmissionLower.KoalaGateChunkSums
import ProximityPrize.SubmissionLower.KoalaSplitGateWords

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000

set_option linter.defProp false

namespace KoalaAt2428Gate37
open KoalaGateSharedData
open FadicGate KoalaGateCheck
open KoalaWeightedRate (Envelope)
open KoalaFarBridge (rowCheck plainCheck)

def envelope : Envelope :=
  ⟨136,54,8,137,54,3536,4437,⟨8816212192,47167846811,29825942379⟩,3891468361361⟩
abbrev split:ℕ:=48
abbrev unit:ℕ:=1919967751680
abbrev terminal:ℕ:=68
abbrev gate:=KoalaSplitRow.rate envelope split unit

private def boxesTape : List (List Entry) := [
  b05k,b04t,b040,b03z,b033,b022,b010,b00w,
  bzz,bzv,bys,bxc,bxb,bvt,bvs,buc,
  bu9,bt2,bt0,bsy,bs2,bqz,bpu,bol,
  bn5,bll,blk,bk3,bk2,big,bie,bfm,
  bfj,bbb,bbc,b5o,b4s,b4t,b4v,b4x,
  b4z,b4l,b4m,b4n,b4o,b4p,b4q,b4r,
  b58,b5m,b5l]
def boxes (r : ℕ) : List FadicGate.Entry :=
  if r < 17 then [] else boxesTape.getD (r-17) []

def plain : ℕ → ℕ × ℕ × ℕ
  | _ => (0,0,0)

private def powersTape : List String := [
  "","","","","","","","",
  "","","","","","","","",
  "","!#","!#&","!#&","!#&+",z3r,z4D,z2Q,
  "!#%(,7<","!#%)-27",z46,"!#%(.2:HF",z6Z,"!#%(+3<<JL","!#$',/7<LJ","!#$',/4=ML[",
  "!#$'*05>GMS","!#$'*05?AOMl","!#$'+16@?QOd","!#$'+-7;@SQ[","!#$&).37AMSRs","!#$&).28BFTSk~#!","!#$&*.28CBVTc~#&~#!","!#$&*/39DCXVZz~#&~#!",
  "!#$&),3:?DRXVr~#)~#&~#!","!#$&),4::ELZXj~#-~#)~#&~#!","!#$&),06:FE]Zb~#%~#-~#)~#&","!#$&)-04;GF_]Zz~#1~#-~#)~##","!#$&(-04<HGW_]q~#5~#1~#-~#)","!#$%(+05<CHQ`_i~#,~#5~#1~#-~##","!##%(+15=>IKb`a~#$~#8~#5~#1~#-","!##%(+16>=JIdb`y~#<~#8~#5~#1~##",
  "!!#%'+.6:>KJ^dbq~#4~#<~#8~#5~#/","!!#%',.36>LKWfdi~#,~#?~#<~#8~#5~##","!!#%(*.27?GLPgfd~#$~#C~#?~#<~#8~#.","!!#%(*/27@BMLigfx~#;~#C~#?~#:~#6~#!","!!#%'*/28@@NMcigo~#3~#G~#B~#=~#8~#+","!!#%'*/38A@PN]kig~#*~#J~#F~#A~#8~#+","!!#%'+,39=AQPVmki~!~~#A~#I~#D~#8~#+","!!#%')-399BLQPomio~#8~#L~#D~#8~#+",
  "!!#%')-069CGRQinid~#)~#Q~#D~#8~#+","!!#$')-04:CCSQ`nidt~#?~#D~#8~#+","!!#$'*-04:DCSQVnidb~#.~#D~#8~#+","!!#%'*.05;ECSQNnid_y~#D~#8~#+","!!#$&)+15;@CMQNeid_g~#3~#8~#+","!!#$&),15;:CFQNZid_Y~!~~#8~#+","!!#$&),15;:CAQNQid_Yl~#8~#+","!!#$&),.57:CAQNKid_YY~#&~#+",
  "!!#$&),.24:CAQNK`d_YTq~#+","!!#$&(,.14:CAJNKUd_YT_~#+","!!#$&(*.14:>ACNKLd_YTOv"]

def powers (r : ℕ) : List ℕ :=
  if r=0 then [] else KoalaSplitGateWords.powers (powersTape.getD (r-1) "")

def plainPowers : ℕ → List ℕ
  | _ => []

def tailPowers : List ℕ := KoalaSplitGateWords.powers "!!#$&(*.14:9B@NLIe`ZUQh~#!sfXL?3"

def priced (r:ℕ):Bool:=rowCheck gate r (boxes r) (powers r) (plain r) (plainPowers r)
private theorem priced_list : (List.range 67).all (fun i => priced (i+1)) = true := by decide +kernel

theorem prices {r : ℕ} (hr : 0 < r) (hR : r < terminal) : priced r = true :=
  price hr hR priced_list

theorem tail:plainCheck gate terminal (4012,1650,550) tailPowers=true:=by decide +kernel

private abbrev Chunk (i n v : ℕ) := lossChunk 12 envelope plain boxes i n = v
private theorem checkPart (i n v : ℕ) (ok : Chunk i n v := by decide +kernel) : Chunk i n v := ok
private def part0 := checkPart 0 6 0x2384dc4cc14
private def part1 := checkPart 6 6 0x2384dc4cc14
private def part2 := checkPart 12 6 0x237df1fdb60
private def part3 := checkPart 18 6 0x23230b91003
private def part4 := checkPart 24 6 0x224fe2953ca
private def part5 := checkPart 30 6 0x20c5f687997
private def part6 := checkPart 36 6 0x1e110cf56be
private def part7 := checkPart 42 6 0x19cbe2d4129
private def part8 := checkPart 48 6 0x138da387c03
private def part9 := checkPart 54 6 0xbfd4ff0683
private def part10 := checkPart 60 6 0x5ec1355041
private def part11 := checkPart 66 1 0x91919cfa4

theorem loss_bound (N : ℕ) : Bound envelope terminal plain boxes 20797866871614 N :=
  loss_of_chunks 12 envelope terminal plain boxes 20797866871614 N (by decide) (by decide)
    (LossSum.empty _ _ _ _
      |>.append 6 0x2384dc4cc14 part0 |>.append 6 0x2384dc4cc14 part1 |>.append 6 0x237df1fdb60 part2 |>.append 6 0x23230b91003 part3
      |>.append 6 0x224fe2953ca part4 |>.append 6 0x20c5f687997 part5 |>.append 6 0x1e110cf56be part6 |>.append 6 0x19cbe2d4129 part7
      |>.append 6 0x138da387c03 part8 |>.append 6 0xbfd4ff0683 part9 |>.append 6 0x5ec1355041 part10 |>.append 1 0x91919cfa4 part11)

def receipt : KoalaSplitProof.Receipt envelope split unit :=
  ⟨terminal, plain, boxes, powers, plainPowers, tailPowers, 20797866871614,
    by decide,by decide,loss_bound,fun _ h h' => prices h h', tail⟩

end KoalaAt2428Gate37

#print axioms KoalaAt2428Gate37.loss_bound
#print axioms KoalaAt2428Gate37.receipt
