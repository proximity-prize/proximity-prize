import ProximityPrize.SubmissionLower.KoalaGateSharedData
import ProximityPrize.SubmissionLower.FadicRisingGate
import ProximityPrize.SubmissionLower.KoalaSplitGateWords

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000

set_option linter.defProp false

namespace KoalaAt2428Gate57
open KoalaGateSharedData
open FadicGate KoalaGateCheck
open KoalaWeightedRate (Envelope)
open KoalaFarBridge (rowCheck plainCheck)

def envelope : Envelope :=
  ⟨136,53,2,137,53,3536,4437,⟨8674575833,51475207921,12125766808⟩,3855263556540⟩
abbrev split:ℕ:=48
abbrev unit:ℕ:=1919968748160
abbrev terminal:ℕ:=66
abbrev gate:=KoalaSplitRow.rate envelope split unit

private def boxesTape : List (List Entry) := [
  b05k,b04t,b040,b03z,b033,b022,b010,b00w,
  bzz,bzv,bys,bxc,bxb,bvt,bvs,buc,
  bu9,bt2,bt0,bsy,bs2,bqz,bpu,bol,
  bn5,bll,blk,bk3,bk2,big,bie,bfm,
  bfj,bbb,bbc,b5o,b4s,b4t,b4v,b4x,
  b4z,b4l,b4m,b4n,b4o,b4p,b4q,b4r,
  b58]
def boxes (r : ℕ) : List FadicGate.Entry :=
  if r < 17 then [] else boxesTape.getD (r-17) []

def plain : ℕ → ℕ × ℕ × ℕ
  | _ => (0,0,0)

private def powersTape : List String := [
  "","","","","","","","",
  "","","","","","","","",
  "","!#","!#&","!#&","!#&+",z4E,z4D,z2Q,
  "!#%(,7<",z3g,z46,"!#%(.29GF",z6Y,z6M,z48,z66,
  "!#$'*05=GMQ","!#$'*05>@OMj","!#$'*06?>POb",z5r,"!#$&)-27@LRPr","!#$&).17AFTRi}",z6h,"!#$&*.29CBWUXy~#$}",
  z6J,z5v,z5d,"!#$&)-/4;FE][Yx~#/~#+~#'~!~","!#$&(-04;HFV][o~#2~#/~#+~#'","!#$%(+05<CHP_]g~#*~#2~#/~#+~!~","!##%(+05=>IJa_^~#!~#6~#2~#/~#+","!##%(+16==JIca_v~#9~#6~#2~#/~!~",
  "!!#%'+.69=KJ]can~#1~#9~#6~#2~#-","!!#%',.36>LKUecf~#)~#=~#9~#6~#2~!~","!!#%'*.17?GLOfec~!~~#A~#=~#9~#5~#,","!!#%(*.27?BMLhfeu~#9~#A~#=~#8~#3}","!!#%'*/27@?NMbhfl~#0~#D~#@~#;~#4~#(","!!#%'*/28A@ON[jhf~#'~#H~#C~#?~#4~#(","!!#%'*,38<APOUljg{~#>~#F~#A~#4~#(","!!#%')-398AKPOnlgk~#5~#J~#A~#4~#(",
  "!!#%&)-059BFQOglgb~#%~#M~#A~#4~#(","!!#$')-049CBRO^lgbp~#;~#A~#4~#(","!!#$')-04:CBROTlgb^~#*~#A~#4~#(","!!#$'*-04:DBROMlgb]u~#A~#4~#(","!!#$&(+05:?BLOMcgb]c~#/~#4~#(","!!#$&)+15::BEOMXgb]Xz~#4~#(","!!#$&),15:9B@OMOgb]Xi~#4~#(","!!#$&),.569B@OMJgb]XV~##~#(",
  "!!#$&),.149B@OMJ^b]XSn~#("]

def powers (r : ℕ) : List ℕ :=
  if r=0 then [] else KoalaSplitGateWords.powers (powersTape.getD (r-1) "")

def plainPowers : ℕ → List ℕ
  | _ => []

def tailPowers : List ℕ := KoalaSplitGateWords.powers "!!#$&(,.04:CAJNKVe`ZUd~#/~##th[OC8"

def priced (r:ℕ):Bool:=rowCheck gate r (boxes r) (powers r) (plain r) (plainPowers r)
private theorem priced_list : (List.range 65).all (fun i => priced (i+1)) = true := by decide +kernel

theorem prices {r : ℕ} (hr : 0 < r) (hR : r < terminal) : priced r = true :=
  price hr hR priced_list

theorem tail:plainCheck gate terminal (4012,1650,550) tailPowers=true:=by decide +kernel

private abbrev Chunk (i n v : ℕ) := lossChunk 16 envelope plain boxes i n = v
private theorem checkPart (i n v : ℕ) (ok : Chunk i n v := by
    unfold Chunk
    rw [← KoalaGateCheck.lossChunkRising_eq]
    decide +kernel) : Chunk i n v := ok
private def part0 := checkPart 0 6 0x2384dc4cc14
private def part1 := checkPart 6 6 0x2384dc4cc14
private def part2 := checkPart 12 6 0x237e166186b
private def part3 := checkPart 18 6 0x23251786d53
private def part4 := checkPart 24 6 0x2256851d092
private def part5 := checkPart 30 6 0x20d55d30ae3
private def part6 := checkPart 36 6 0x1e302084839
private def part7 := checkPart 42 6 0x1a03d150641
private def part8 := checkPart 48 6 0x13ea95654df
private def part9 := checkPart 54 6 0xc88808f95d
private def part10 := checkPart 60 5 0x5d21fe2e60

theorem loss_bound (N : ℕ) : Bound envelope terminal plain boxes 20843996890225 N :=
  loss_of_chunks 16 envelope terminal plain boxes 20843996890225 N (by decide) (by decide)
    (LossSum.empty _ _ _ _
      |>.append 6 0x2384dc4cc14 part0 |>.append 6 0x2384dc4cc14 part1 |>.append 6 0x237e166186b part2 |>.append 6 0x23251786d53 part3
      |>.append 6 0x2256851d092 part4 |>.append 6 0x20d55d30ae3 part5 |>.append 6 0x1e302084839 part6 |>.append 6 0x1a03d150641 part7
      |>.append 6 0x13ea95654df part8 |>.append 6 0xc88808f95d part9 |>.append 5 0x5d21fe2e60 part10)

def receipt : KoalaSplitProof.Receipt envelope split unit :=
  ⟨terminal, plain, boxes, powers, plainPowers, tailPowers, 20843996890225,
    by decide,by decide,loss_bound,fun _ h h' => prices h h', tail⟩

end KoalaAt2428Gate57

#print axioms KoalaAt2428Gate57.loss_bound
#print axioms KoalaAt2428Gate57.receipt
