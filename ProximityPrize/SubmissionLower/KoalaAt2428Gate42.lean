import ProximityPrize.SubmissionLower.KoalaGateSharedData
import ProximityPrize.SubmissionLower.KoalaGateChunkSums
import ProximityPrize.SubmissionLower.KoalaSplitGateWords

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000

set_option linter.defProp false

namespace KoalaAt2428Gate42
open KoalaGateSharedData
open FadicGate KoalaGateCheck
open KoalaWeightedRate (Envelope)
open KoalaFarBridge (rowCheck plainCheck)

def envelope : Envelope :=
  ⟨120,56,3,123,56,3120,4423,⟨10182478089,47755231059,12303933557⟩,3912707741141⟩
abbrev split:ℕ:=48
abbrev unit:ℕ:=1919967853440
abbrev terminal:ℕ:=66
abbrev gate:=KoalaSplitRow.rate envelope split unit

private def boxesTape : List (List Entry) := [
  b05l,b04u,b03z,b033,b022,b023,b00w,b00y,
  bzv,bys,bxc,bxb,bvt,bvs,buc,bu9,
  bua,bt0,bsy,bs2,bqz,bpu,bol,bn5,
  bll,blk,bk3,bk2,big,bie,bfm,bfj,
  bbb,bbf,b71,b7j,b7z,b5r,b5s,b5u,
  b5v,b5w,b5x,b5y,b5z,b60,b12.take 23,b13.take 23]
def boxes (r : ℕ) : List FadicGate.Entry :=
  if r < 18 then [] else boxesTape.getD (r-18) []

def plain : ℕ → ℕ × ℕ × ℕ
  | _ => (0,0,0)

private def powersTape : List String := [
  "","","","","","","","",
  "","","","","","","","",
  "","","!#","!#&","!#&+",z3r,z3O,z2Q,
  z4a,z3g,z46,"!#%(.29HF","!#%(+3:BH","!#%(+3;;IK",z48,z66,
  "!#$'*05=GMR","!#$'*05>AOM","!#$'+16?>QOc","!#$'+-7;?RQZ","!#$&)-37ALRQs","!#$&).17BFTRj~#!","!#$&*.28CBVTb~#%~#!","!#$&*.29DCXVYz~#%~#!",
  "!#$&(,39?DQXVq~#)~#%~#!","!#$&),3::EKYXi~#,~#)~#%~#!","!#$%),06:FE[Ya~#$~#,~#)~#%","!#$&)-/4;GF^[Yy~#0~#,~#)~#!","!#$&(-04;HGW^[p~#4~#0~#,~#)","!#$%(+05<CHQ`^h~#+~#4~#0~#,~#!","!##%(+05=>IJb`_~##~#7~#4~#0~#,","!##%(+16==JIcb`x~#;~#7~#4~#0~#!",
  "!!#%'+.69=KJ]cbp~#3~#;~#7~#4~#.","!!#%',.36>LKVecg~#*~#?~#;~#7~#4~#!","!!#%(*.27?GLPgec~#!~#B~#?~#;~#7~#.","!!#%(*.27?BMLigew~#:~#B~#?~#;~#4~#!","!!#%'*/28@?NMbign~#2~#F~#B~#>~#5~#(","!!#%'*/38A@ON[jif~#)~#I~#F~#@~#5~#(","!!#%'+,38=APOUljg{~#A~#I~#A~#5~#(","!!#%')-398AKPOnkgk~#6~#L~#A~#5~#(",
  "!!#%&)-059BFQOglgb~#%~#N~#A~#5~#(","!!#$')-049CBRO^lgbp~#<~#A~#5~#(","!!#$'*-04:CBROTlgb^~#*~#A~#5~#(","!!#$'*-04:DBROMlgb^u~#A~#5~#(","!!#$&(+04:?BLOMcgb^d~#/~#5~#(","!!#$&)+15::BEOMXgb^X{~#5~#(","!!#$&),15:9B@OMOgb^Xi~#5~#(","!!#$&),.569B@OMJgb^XV~##~#(",
  "!!#$&),.149B@OMJ^b^XSn~#("]

def powers (r : ℕ) : List ℕ :=
  if r=0 then [] else KoalaSplitGateWords.powers (powersTape.getD (r-1) "")

def plainPowers : ℕ → List ℕ
  | _ => []

def tailPowers : List ℕ := KoalaSplitGateWords.powers "!!#$&(,.04:CAJNKVe`ZUd~#0~#$uh[OC7"

def priced (r:ℕ):Bool:=rowCheck gate r (boxes r) (powers r) (plain r) (plainPowers r)
private theorem priced_list : (List.range 65).all (fun i => priced (i+1)) = true := by decide +kernel

theorem prices {r : ℕ} (hr : 0 < r) (hR : r < terminal) : priced r = true :=
  price hr hR priced_list

theorem tail:plainCheck gate terminal (4012,1650,550) tailPowers=true:=by decide +kernel

private abbrev Chunk (i n v : ℕ) := lossChunk 16 envelope plain boxes i n = v
private theorem checkPart (i n v : ℕ) (ok : Chunk i n v := by decide +kernel) : Chunk i n v := ok
private def part0 := checkPart 0 6 0x2384dc4cc14
private def part1 := checkPart 6 6 0x2384dc4cc14
private def part2 := checkPart 12 6 0x23824f051a5
private def part3 := checkPart 18 6 0x2328b234b70
private def part4 := checkPart 24 6 0x225710611a9
private def part5 := checkPart 30 6 0x20d3b7516e5
private def part6 := checkPart 36 6 0x1e286b5d1b9
private def part7 := checkPart 42 6 0x19f5b0c6b17
private def part8 := checkPart 48 6 0x13d3104872b
private def part9 := checkPart 54 6 0xc7f77efac8
private def part10 := checkPart 60 5 0x5dcd203ca2

theorem loss_bound (N : ℕ) : Bound envelope terminal plain boxes 20834072549680 N :=
  loss_of_chunks 16 envelope terminal plain boxes 20834072549680 N (by decide) (by decide)
    (LossSum.empty _ _ _ _
      |>.append 6 0x2384dc4cc14 part0 |>.append 6 0x2384dc4cc14 part1 |>.append 6 0x23824f051a5 part2 |>.append 6 0x2328b234b70 part3
      |>.append 6 0x225710611a9 part4 |>.append 6 0x20d3b7516e5 part5 |>.append 6 0x1e286b5d1b9 part6 |>.append 6 0x19f5b0c6b17 part7
      |>.append 6 0x13d3104872b part8 |>.append 6 0xc7f77efac8 part9 |>.append 5 0x5dcd203ca2 part10)

def receipt : KoalaSplitProof.Receipt envelope split unit :=
  ⟨terminal, plain, boxes, powers, plainPowers, tailPowers, 20834072549680,
    by decide,by decide,loss_bound,fun _ h h' => prices h h', tail⟩

end KoalaAt2428Gate42

#print axioms KoalaAt2428Gate42.loss_bound
#print axioms KoalaAt2428Gate42.receipt
