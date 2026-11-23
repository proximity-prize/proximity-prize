import ProximityPrize.SubmissionLower.KoalaGateSharedData
import ProximityPrize.SubmissionLower.KoalaGateChunkSums
import ProximityPrize.SubmissionLower.KoalaSplitGateWords

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000

set_option linter.defProp false

namespace KoalaAt2428Gate40
open KoalaGateSharedData
open FadicGate KoalaGateCheck
open KoalaWeightedRate (Envelope)
open KoalaFarBridge (rowCheck plainCheck)

def envelope : Envelope :=
  ⟨136,54,4,137,54,3536,4437,⟨7294666054,34351274666,73078997125⟩,3182174438942⟩
abbrev split:ℕ:=48
abbrev unit:ℕ:=1919967294720
abbrev terminal:ℕ:=66
abbrev gate:=KoalaSplitRow.rate envelope split unit

private def boxesTape : List (List Entry) := [
  b05o,b04x,b043,b035,b023,b027,b00y,bzv,
  bzx,byt,bxb,bxg,bvs,bvv,bu9,bua,
  bt0,bsy,bs2,bs1,brz,bpx,bor,bn9,
  blk,bln,bk2,bk5,bie,bifAtom,bfj,bfl,
  bbc,bbv,b4s,b4t,b4v,b4x,b4z,b4l,
  b4m,b4n,b4o,b4p,b4q,b4r,b58]
def boxes (r : ℕ) : List FadicGate.Entry :=
  if r < 19 then [] else boxesTape.getD (r-19) []

def plain : ℕ → ℕ × ℕ × ℕ
  | _ => (0,0,0)

private def powersTape : List String := [
  "","","","","","","","",
  "","","","","","","","",
  "","","","!#","!#%","!#&)",z3O,z3O,
  "!#%(,6",z4I,"!#%(-07","!#%'-18E","!#$'+29?E","!#$(+2:9F","!#$'+.5:HF","!#$',.3;JH",
  "!#$'*/4<DJJ","!#$&*/4==KJ","!#$&*05>=MKY","!#$'*-69>OMP","!#$&)-16?HOMh","!#$&)-16@BPO`","!#$&).17A@RPV","!#$&).27BATRPnv",
  "!#$&(+28=BMTRfyv","!#$&(,298CGUT^|yv","!#$%(,/59DCWUVu|yv","!#$%),/39DDYWUm~##|y","!##&(,/3:FDRYWd~#&~##|y","!##%(*/4;AFLZY[{~#&~##|","!##%(+04;<GF]ZYs~#)~#&~##|","!##%(+05<;GG^]Zk~#,~#)~#&~##",
  "!!#%'+-58<HGW^]c~#$~#,~#)~#&~!~","!!#%'+-25=IHQ`^[z~#/~#,~#)~#&","!!#%'*.16=EIKb`^r~#3~#/~#,~#)}","!!#%'*.16>@JIdb`j~#+~#3~#/~#+~#(","!!#%'*.17?>KJ]dbb~##~#6~#2~#.~#,}","!!#%'*.27??LKVedbx~#9~#5~#2~#,}","!!#%'*,27;?MLQgfep~#1~#8~#7~#,}","!!#%'),287@INMigee~#)~#;~#7~#,}",
  "!!#%&),/48ADOOcje`z~#B~#7~#,}","!!#$&)-/38AAPO[je`j~#2~#7~#,}","!!#$&)-/39BBQORje`[~#!~#7~#,}","!!#$')-049CBQOLje`[o~#7~#,}","!!#$&(+04:>BKOLae`[^~#'~#,}","!!#$&(+05:9BDOLVe`[Vt~#,}","!!#$&(+15:9B@OLMe`[Vc~#,}","!!#$&),.569B@OLIe`[VRy}",
  "!!#$&),.149B@OLI[`[VQh}"]

def powers (r : ℕ) : List ℕ :=
  if r=0 then [] else KoalaSplitGateWords.powers (powersTape.getD (r-1) "")

def plainPowers : ℕ → List ℕ
  | _ => []

def tailPowers : List ℕ := KoalaSplitGateWords.powers "!!#$&(,.049B@IMJSb]WS[~#$vk_SH=2"

def priced (r:ℕ):Bool:=rowCheck gate r (boxes r) (powers r) (plain r) (plainPowers r)
private theorem priced_list : (List.range 65).all (fun i => priced (i+1)) = true := by decide +kernel

theorem prices {r : ℕ} (hr : 0 < r) (hR : r < terminal) : priced r = true :=
  price hr hR priced_list

theorem tail:plainCheck gate terminal (4012,1650,550) tailPowers=true:=by decide +kernel

private abbrev Chunk (i n v : ℕ) := lossChunk 16 envelope plain boxes i n = v
private theorem checkPart (i n v : ℕ) (ok : Chunk i n v := by decide +kernel) : Chunk i n v := ok
private def part0 := checkPart 0 6 0x2384dc4cc14
private def part1 := checkPart 6 6 0x2384dc4cc14
private def part2 := checkPart 12 6 0x2384dc4cc14
private def part3 := checkPart 18 6 0x233440d8762
private def part4 := checkPart 24 6 0x225c3f31ead
private def part5 := checkPart 30 6 0x20d15fa4355
private def part6 := checkPart 36 6 0x1e2d0cb67ec
private def part7 := checkPart 42 6 0x19eb8531363
private def part8 := checkPart 48 6 0x13bad0913db
private def part9 := checkPart 54 6 0xc3b9e26ede
private def part10 := checkPart 60 5 0x584058e619

theorem loss_bound (N : ℕ) : Bound envelope terminal plain boxes 20788575744449 N :=
  loss_of_chunks 16 envelope terminal plain boxes 20788575744449 N (by decide) (by decide)
    (LossSum.empty _ _ _ _
      |>.append 6 0x2384dc4cc14 part0 |>.append 6 0x2384dc4cc14 part1 |>.append 6 0x2384dc4cc14 part2 |>.append 6 0x233440d8762 part3
      |>.append 6 0x225c3f31ead part4 |>.append 6 0x20d15fa4355 part5 |>.append 6 0x1e2d0cb67ec part6 |>.append 6 0x19eb8531363 part7
      |>.append 6 0x13bad0913db part8 |>.append 6 0xc3b9e26ede part9 |>.append 5 0x584058e619 part10)

def receipt : KoalaSplitProof.Receipt envelope split unit :=
  ⟨terminal, plain, boxes, powers, plainPowers, tailPowers, 20788575744449,
    by decide,by decide,loss_bound,fun _ h h' => prices h h', tail⟩

end KoalaAt2428Gate40

#print axioms KoalaAt2428Gate40.loss_bound
#print axioms KoalaAt2428Gate40.receipt
