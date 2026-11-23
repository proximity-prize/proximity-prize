import ProximityPrize.SubmissionLower.KoalaAt2428Gate37
import ProximityPrize.SubmissionLower.KoalaGateSharedData
import ProximityPrize.SubmissionLower.KoalaGateChunkSums
import ProximityPrize.SubmissionLower.KoalaSplitGateWords

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000

set_option linter.defProp false

namespace KoalaAt2428Gate38
open KoalaGateSharedData
open FadicGate KoalaGateCheck
open KoalaWeightedRate (Envelope)
open KoalaFarBridge (rowCheck plainCheck)

def envelope : Envelope :=
  ⟨132,54,12,135,54,3432,4435,⟨9159343958,51851329012,9701836134⟩,3985636935723⟩
abbrev split:ℕ:=48
abbrev unit:ℕ:=1919968473600
abbrev terminal:ℕ:=67
abbrev gate:=KoalaSplitRow.rate envelope split unit

private def boxesTape : List (List Entry) := [
  b05k,b04t,b040,b03z,b033,b022,b010,b00w,
  bzz,bzv,bys,bxc,bxb,bvt,bvs,buc,
  bu9,bt2,bt0,bsy,bs2,bqz,bpu,bol,
  bn5,bll,blk,bk3.take 18++unpack 1 0x1bac5b78,bk2,big.take 19++unpack 1 0x1bac5b78,bie,bfm.take 20++unpack 1 0x1bac5b78,
  bfj.take 20++unpack 1 0x20663e65,bbb.take 21++unpack 1 0x1bac5b78,bbe.take 21++unpack 1 0x20663e62,b5p.take 22++unpack 1 0x1bac7850,b59,b4u,b4w,b4y,
  b50,b51,b52,b53,b54,b55,b56,b57,
  b5k,b5n]
def boxes (r : ℕ) : List FadicGate.Entry :=
  if r < 17 then [] else boxesTape.getD (r-17) []

def plain : ℕ → ℕ × ℕ × ℕ
  | _ => (0,0,0)

private def powersTape : List String := [
  "","","","","","","","",
  "","","","","","","","",
  "","!#","!#&","!#&","!#&+",z3r,z4D,z2Q,
  "!#%(,7=",z3g,z46,"!#%(.2:HF",z6Z,"!#%(+3<<JL","!#$',/7<LJ","!#$',/4=ML]",
  "!#$'*05>GMT","!#$'*05?AOMl","!#$'+16@?QOd","!#$'+-7;@SQ[","!#$&).37AMSRt","!#$&).28BFUSl~##","!#$&*.28CBVUc~#'~##","!#$&*/39DCXVZ{~#'~##",
  "!#$&(,3:?DRXVs~#*~#'~##","!#$&),3::ELZXk~#.~#*~#'~##","!#$&),06:FE]Zc~#&~#.~#*~#'","!#$&)-04;GF_]Z{~#2~#.~#*~##","!#$&(-04<HGW_]r~#6~#2~#.~#*","!#$%(+05<CHQ`_j~#-~#6~#2~#.~##","!##%(+15=>IKb`a~#%~#9~#6~#2~#.","!##%(+16>=JIdb`z~#=~#9~#6~#2~##",
  "!!#%'+.6:>KJ^dbq~#5~#=~#9~#6~#/","!!#%',.36>LKWfdi~#,~#@~#=~#9~#6~##","!!#%(*.27?GLPhfd~#$~#D~#@~#=~#9~#/","!!#%(*.27@BMLihfy~#<~#D~#@~#<~#8~##","!!#%'*/28@@NMcihp~#4~#H~#D~#?~#8~#+","!!#%'*/38A@ON]kih~#+~#L~#H~#C~#8~#+","!!#%'+,39=AQPVmki~#!~#C~#K~#E~#8~#+","!!#%')-399BLQPomin~#:~#N~#E~#8~#+",
  "!!#%&)-069BGRPinid~#)~#Q~#E~#8~#+","!!#$')-04:CBSP`nidt~#@~#E~#8~#+","!!#$'*-04:DCSPUnidb~#.~#E~#8~#+","!!#%'*-04;DCSPMnid_y~#E~#8~#+","!!#$&)+15;?CLPMdid_g~#3~#8~#+","!!#$&),15;:CFPMZid_Y~!~~#8~#+","!!#$&),15;:CAPMPid_Yl~#8~#+","!!#$&),.57:CAPMKid_YY~#&~#+",
  "!!#$&),.14:CAPMK_d_YTq~#+","!!#$&(,.04:CAJMKUd_YT_~#+"]

def powers (r : ℕ) : List ℕ :=
  if r=0 then [] else KoalaSplitGateWords.powers (powersTape.getD (r-1) "")

def plainPowers : ℕ → List ℕ
  | _ => []

def tailPowers : List ℕ := KoalaSplitGateWords.powers "!!#$&(*.04:>ADNLMe`[VR|~#$uh[NB5)"

def priced (r:ℕ):Bool:=rowCheck gate r (boxes r) (powers r) (plain r) (plainPowers r)
private theorem priced_list : (List.range 66).all (fun i => priced (i+1)) = true := by decide +kernel

theorem prices {r : ℕ} (hr : 0 < r) (hR : r < terminal) : priced r = true :=
  price hr hR priced_list

theorem tail:plainCheck gate terminal (4012,1650,550) tailPowers=true:=by decide +kernel

private abbrev Chunk (i n v : ℕ) := lossChunk 12 envelope plain boxes i n = v
private theorem checkPart (i n v : ℕ) (ok : Chunk i n v := by decide +kernel) : Chunk i n v := ok
private def part0 := checkPart 0 6 0x2384dc4cc14
private def part1 := checkPart 6 6 0x2384dc4cc14
private def part2 := checkPart 12 6 0x237dfba0fac
private def part3 := checkPart 18 6 0x23239c7a93e
private def part4 := checkPart 24 6 0x2251be50969
private def part5 := checkPart 30 6 0x20ca5205a67
private def part6 := checkPart 36 6 0x1e19d3345e8
private def part7 := checkPart 42 6 0x19dc02f063b
private def part8 := checkPart 48 6 0x13a6a1d3855
private def part9 := checkPart 54 6 0xc1e40c9833
private def part10 := checkPart 60 6 0x61661e56c1

theorem loss_bound (N : ℕ) : Bound envelope terminal plain boxes 20794213869646 N :=
  loss_of_chunks 12 envelope terminal plain boxes 20794213869646 N (by decide) (by decide)
    (LossSum.empty _ _ _ _
      |>.append 6 0x2384dc4cc14 part0 |>.append 6 0x2384dc4cc14 part1 |>.append 6 0x237dfba0fac part2 |>.append 6 0x23239c7a93e part3
      |>.append 6 0x2251be50969 part4 |>.append 6 0x20ca5205a67 part5 |>.append 6 0x1e19d3345e8 part6 |>.append 6 0x19dc02f063b part7
      |>.append 6 0x13a6a1d3855 part8 |>.append 6 0xc1e40c9833 part9 |>.append 6 0x61661e56c1 part10)

def receipt : KoalaSplitProof.Receipt envelope split unit :=
  ⟨terminal, plain, boxes, powers, plainPowers, tailPowers, 20794213869646,
    by decide,by decide,loss_bound,fun _ h h' => prices h h', tail⟩

end KoalaAt2428Gate38

#print axioms KoalaAt2428Gate38.loss_bound
#print axioms KoalaAt2428Gate38.receipt
