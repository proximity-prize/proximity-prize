import ProximityPrize.SubmissionLower.KoalaGateSharedData
import ProximityPrize.SubmissionLower.KoalaGateChunkSums
import ProximityPrize.SubmissionLower.KoalaSplitGateWords

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000

set_option linter.defProp false

namespace KoalaAt2428Gate43
open KoalaGateSharedData
open FadicGate KoalaGateCheck
open KoalaWeightedRate (Envelope)
open KoalaFarBridge (rowCheck plainCheck)

def envelope : Envelope :=
  ⟨124,55,3,127,55,3224,4427,⟨9654018584,48812138280,11551150290⟩,3879230820182⟩
abbrev split:ℕ:=48
abbrev unit:ℕ:=1919967636480
abbrev terminal:ℕ:=66
abbrev gate:=KoalaSplitRow.rate envelope split unit

private def boxesTape : List (List Entry) := [
  b05l,b04u,b03z,b033,b022,b023,b00w,b00y,
  bzv,bys,bxc,bxb,bvt,bvs,buc,bu9,
  bua,bt0,bsy,bs2,bqz,bpu,bol,bn5,
  bll,blk,bk3,bk2,big,bie,bfm,bfj,
  bbb,bbf,b72,b5q,b5c,b5d,b5e,b5f,
  b5g,b5h,b5i,b5a,b5b,b5j,b5t,b61]
def boxes (r : ℕ) : List FadicGate.Entry :=
  if r < 18 then [] else boxesTape.getD (r-18) []

def plain : ℕ → ℕ × ℕ × ℕ
  | _ => (0,0,0)

private def powersTape : List String := [
  "","","","","","","","",
  "","","","","","","","",
  "","","!#","!#&","!#&+",z4E,z3O,z2Q,
  z4a,z3g,z46,"!#%'.29GF","!#%(+2:AG",z6M,z48,z66,
  "!#$'*/5=FMQ","!#$&*05>@NM","!#$'*06?>PNb",z5r,"!#$&)-27@LRPr","!#$&).17AETRi}",z6h,"!#$&*.28CBWUWx~#$}",
  z6J,z5v,z5d,"!#$&)-/4:FE][Yx~#/~#+~#'~!~","!#$&(-04;GFV][o~#2~#/~#+~#'","!#$%(+05<CGP_]g~#*~#2~#/~#+~!~","!##%(+05=>HJa_^~#!~#6~#2~#/~#+","!##%(+16==IHca_v~#9~#6~#2~#/~!~",
  "!!#%'+.69=JI]can~#1~#9~#6~#2~#-","!!#%'+.26>LJUecf~#)~#=~#9~#6~#2~!~","!!#%'*.16?GLOfec~!~~#A~#=~#9~#6~#-","!!#%(*.27?BMLhfeu~#9~#A~#=~#9~#6~!~","!!#%'*/27@?NMbhfm~#0~#D~#A~#=~#7~#*","!!#%'*/28A@ON[jhf~#(~#H~#D~#A~#7~#*","!!#%'*,38<APOTkjh|~#?~#H~#C~#7~#*","!!#%'),398AKPOmkhl~#7~#K~#C~#7~#*",
  "!!#%&)-059BFQPgmhc~#&~#O~#C~#7~#*","!!#$')-039BBRP^mhcr~#=~#C~#7~#*","!!#$')-04:CBRPTmhc`~#,~#C~#7~#*","!!#$'*-04:DBRPMmhc^w~#C~#7~#*","!!#$&(+04:?BLPMchc^e~#1~#7~#*","!!#$&)+15::BEPMYhc^X|~#7~#*","!!#$&),15:9BAPMOhc^Xk~#7~#*","!!#$&),.569BAPMJhc^XX~#%~#*",
  "!!#$&),.149BAPMJ^c^XSp~#*"]

def powers (r : ℕ) : List ℕ :=
  if r=0 then [] else KoalaSplitGateWords.powers (powersTape.getD (r-1) "")

def plainPowers : ℕ → List ℕ
  | _ => []

def tailPowers : List ℕ := KoalaSplitGateWords.powers "!!#$&(,.04:CAJNKUd`ZUc~#/~##th[OC7+"

def priced (r:ℕ):Bool:=rowCheck gate r (boxes r) (powers r) (plain r) (plainPowers r)
private theorem priced_list : (List.range 65).all (fun i => priced (i+1)) = true := by decide +kernel

theorem prices {r : ℕ} (hr : 0 < r) (hR : r < terminal) : priced r = true :=
  price hr hR priced_list

theorem tail:plainCheck gate terminal (4012,1650,550) tailPowers=true:=by decide +kernel

private abbrev Chunk (i n v : ℕ) := lossChunk 16 envelope plain boxes i n = v
private theorem checkPart (i n v : ℕ) (ok : Chunk i n v := by decide +kernel) : Chunk i n v := ok
private def part0 := checkPart 0 6 0x2384dc4cc14
private def part1 := checkPart 6 6 0x2384dc4cc14
private def part2 := checkPart 12 6 0x238251c0778
private def part3 := checkPart 18 6 0x2329184d8c6
private def part4 := checkPart 24 6 0x225863b41f5
private def part5 := checkPart 30 6 0x20d6ca79122
private def part6 := checkPart 36 6 0x1e2e9b0d7a9
private def part7 := checkPart 42 6 0x1a00e49599f
private def part8 := checkPart 48 6 0x13e397629c7
private def part9 := checkPart 54 6 0xc75276ee78
private def part10 := checkPart 60 5 0x5bb66096ee

theorem loss_bound (N : ℕ) : Bound envelope terminal plain boxes 20832727673842 N :=
  loss_of_chunks 16 envelope terminal plain boxes 20832727673842 N (by decide) (by decide)
    (LossSum.empty _ _ _ _
      |>.append 6 0x2384dc4cc14 part0 |>.append 6 0x2384dc4cc14 part1 |>.append 6 0x238251c0778 part2 |>.append 6 0x2329184d8c6 part3
      |>.append 6 0x225863b41f5 part4 |>.append 6 0x20d6ca79122 part5 |>.append 6 0x1e2e9b0d7a9 part6 |>.append 6 0x1a00e49599f part7
      |>.append 6 0x13e397629c7 part8 |>.append 6 0xc75276ee78 part9 |>.append 5 0x5bb66096ee part10)

def receipt : KoalaSplitProof.Receipt envelope split unit :=
  ⟨terminal, plain, boxes, powers, plainPowers, tailPowers, 20832727673842,
    by decide,by decide,loss_bound,fun _ h h' => prices h h', tail⟩

end KoalaAt2428Gate43

#print axioms KoalaAt2428Gate43.loss_bound
#print axioms KoalaAt2428Gate43.receipt
