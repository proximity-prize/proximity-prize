import ProximityPrize.SubmissionLower.KoalaGateSharedData
import ProximityPrize.SubmissionLower.FadicRisingGate
import ProximityPrize.SubmissionLower.KoalaSplitGateWords

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000

set_option linter.defProp false

namespace KoalaAt2428Gate58
open KoalaGateSharedData
open FadicGate KoalaGateCheck
open KoalaWeightedRate (Envelope)
open KoalaFarBridge (rowCheck plainCheck)

def envelope : Envelope :=
  ⟨136,51,2,136,51,3536,4436,⟨8139618472,50036185890,12361726125⟩,3614407681131⟩
abbrev split:ℕ:=48
abbrev unit:ℕ:=1919967375360
abbrev terminal:ℕ:=64
abbrev gate:=KoalaSplitRow.rate envelope split unit

private def boxesTape : List (List Entry) := [
  b05k,b04t,b040,b03z,b033,b022,b010,b00w,
  bzz,bzv,bys,bxc,bxb,bvt,bvs,buc,
  bu9,bt2,bt0,bsy,bs2,bqz,bpu,bol,
  bn5,bll,blk,bk3,bk2,big,bie,bfm,
  bfj,bbb,bbe.take 21++unpack 1 0x2112e3ff,b6w,b7f,b7w,b86,b8l,
  b8s,b96,b2k.take 11++unpack 12 0x99a740d468a669d0351a299a740d468a669d03516af4cd2b,b2r.take 10++unpack 13 0x4cd3a06a345334e81a8d14cd3a06a345334e81a8d17107b337,b2v.take 9++unpack 14 0x4cd3a06a345334e81a8d14cd3a06a345334e81a8d14cd3a067770cf2f,b33.take 8++unpack 15 0x2669d0351a299a740d468a669d0351a299a740d468a669d03517d83b53b,b39.take 7++unpack 16 0x1334e81a8d14cd3a06a345334e81a8d14cd3a06a345334e81a8d183969b47]
def boxes (r : ℕ) : List FadicGate.Entry :=
  if r < 17 then [] else boxesTape.getD (r-17) []

def plain : ℕ → ℕ × ℕ × ℕ
  | _ => (0,0,0)

private def powersTape : List String := [
  "","","","","","","","",
  "","","","","","","","",
  "","!#","!#&","!#&","!#%+",z4E,"!#%)/4",z4D,
  "!#%(,6:",z4I,"!#%(-17D","!#%'-18FD","!#$(+29?F","!#%(+3:9GF","!#$'+.5:IG","!#$',/3;KIU",
  "!#$'*/4<EKM","!#$&*/4=>LKe","!#$&*05>=NL]","!#$'*-69>PNT","!#$&)-26?IPNl","!#$&)-16@CQPcx","!#$&).17A@SQZ{x","!#$&).28BAUSRs{x",
  "!#$&(+28=BNUSj~!~{x","!#$&(,398CHVUb~#%~!~{x","!#$%),/59DCXVYy~#%~!~{","!#$%),/3:EDZXVq~#(~#%~!~y","!##&(,/4:FETZXi~#,~#(~#%~!~","!##%(*04;AFM[Z`~##~#,~#(~#%y","!##%(+04<<GG^[Zx~#/~#,~#(~#%","!##%(+05<<HG`^[o~#2~#/~#,~#(y",
  "!!#%'+-58<IHY`^g~#*~#2~#/~#,~#&","!!#%'+-25=JIRb`_~#!~#5~#2~#/~#,y","!!#%'*.16=EJLcb`v~#9~#5~#2~#/~#&","!!#%'*.16>@KJecbn~#1~#9~#5~#1~#-x","!!#%'*.27?>LK_ece~#(~#<~#9~#4~#.~#!","!!#%'*.27??MLWgec}~#@~#<~#8~#.~#!","!!#%'*,28;?NMQhgdt~#7~#?~#:~#.~#!","!!#%'),388@INMjhdd~#.~#B~#:~#.~#!",
  "!!#%&),/48ADONdid`z~#E~#:~#.~#!","!!#$&)-/38AAPNZid`i~#4~#:~#.~#!","!!#$&)-/39BAPNQid`Z~##~#:~#.~#!","!!#$')-049CAPNKid`Zo~#:~#.~#!","!!#$&(+04:>AJNK`d`Z^~#(~#.~#!","!!#$&(+04:8ACNKUd`ZUt~#.~#!","!!#$&(+04:8A?NKLd`ZUc~#.~#!"]

def powers (r : ℕ) : List ℕ :=
  if r=0 then [] else KoalaSplitGateWords.powers (powersTape.getD (r-1) "")

def plainPowers : ℕ → List ℕ
  | _ => []

def tailPowers : List ℕ := KoalaSplitGateWords.powers "!!#$&),-469B@OMKhd_Z^~#*~#0~#%wlaUJA"

def priced (r:ℕ):Bool:=rowCheck gate r (boxes r) (powers r) (plain r) (plainPowers r)
private theorem priced_list : (List.range 63).all (fun i => priced (i+1)) = true := by decide +kernel

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
private def part2 := checkPart 12 6 0x237e3d44281
private def part3 := checkPart 18 6 0x23274fbd325
private def part4 := checkPart 24 6 0x225dbef3e37
private def part5 := checkPart 30 6 0x20e6320414c
private def part6 := checkPart 36 6 0x1e5215296b3
private def part7 := checkPart 42 6 0x1a412e05b56
private def part8 := checkPart 48 6 0x144f3e08fa2
private def part9 := checkPart 54 6 0xd18bba2dba
private def part10 := checkPart 60 3 0x43b90ae166

theorem loss_bound (N : ℕ) : Bound envelope terminal plain boxes 20833280048668 N :=
  loss_of_chunks 16 envelope terminal plain boxes 20833280048668 N (by decide) (by decide)
    (LossSum.empty _ _ _ _
      |>.append 6 0x2384dc4cc14 part0 |>.append 6 0x2384dc4cc14 part1 |>.append 6 0x237e3d44281 part2 |>.append 6 0x23274fbd325 part3
      |>.append 6 0x225dbef3e37 part4 |>.append 6 0x20e6320414c part5 |>.append 6 0x1e5215296b3 part6 |>.append 6 0x1a412e05b56 part7
      |>.append 6 0x144f3e08fa2 part8 |>.append 6 0xd18bba2dba part9 |>.append 3 0x43b90ae166 part10)

def receipt : KoalaSplitProof.Receipt envelope split unit :=
  ⟨terminal, plain, boxes, powers, plainPowers, tailPowers, 20833280048668,
    by decide,by decide,loss_bound,fun _ h h' => prices h h', tail⟩

end KoalaAt2428Gate58

#print axioms KoalaAt2428Gate58.loss_bound
#print axioms KoalaAt2428Gate58.receipt
