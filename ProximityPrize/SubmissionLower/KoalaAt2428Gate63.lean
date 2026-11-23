import ProximityPrize.SubmissionLower.KoalaGateSharedData
import ProximityPrize.SubmissionLower.KoalaGateChunkSums
import ProximityPrize.SubmissionLower.KoalaSplitGateWords

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000

set_option linter.defProp false

namespace KoalaAt2428Gate63
open KoalaGateSharedData
open FadicGate KoalaGateCheck
open KoalaWeightedRate (Envelope)
open KoalaFarBridge (rowCheck plainCheck)

def envelope : Envelope :=
  ⟨132,47,8,135,47,3432,4435,⟨6715583099,46184397097,6932833572⟩,2977312059487⟩
abbrev split:ℕ:=48
abbrev unit:ℕ:=1919968020480
abbrev terminal:ℕ:=59
abbrev gate:=KoalaSplitRow.rate envelope split unit

private def boxesTape : List (List Entry) := [
  b05m,b04w,b041,b034,b024,b026,b00z,bzw,
  byp,byq,byr,bxd,bvu,bub,bud,bsz,
  bt1,brz,bs0,bqx,bqw,bps,bpt,bpr,
  bok,bn6,blm,bk4,bih,bfk,bfw,bfx,
  bfy,bby,bbz,bc0,bc1]
def boxes (r : ℕ) : List FadicGate.Entry :=
  if r < 22 then [] else boxesTape.getD (r-22) []

def plain : ℕ → ℕ × ℕ × ℕ
  | _ => (0,0,0)

private def powersTape : List String := [
  "","","","","","","","",
  "","","","","","","","",
  "","","","","","","!#","!#%",
  "!#%'",z3p,"!#$(+",z4C,z65,"!#$'*076","!#$&*-27","!#$&*-18",
  "!#$')-29>","!#$&).298F","!#$&).3:9HF","!#$&)+35:IH","!#$&(,/3;CIH","!#$&(,/4<<JI","!#$&(,/4=<LJJ","!#$%),05>=MLJ",
  "!#$%'*059>GMLX","!#$%(+165?@OMP","!##%(+-26??POLh","!##%(+-17@?RPO_","!##%'+.17A@KRPU","!##%').28<AESROm","!##%'*.288BAUSRdy","!##%'*.298CBVUSZ{y",
  "!!#%'*,359DCOVURs{y","!!#%'*,/39EDIWVTj~!~{y","!!#%'),/3:?ECYWVa~#$~!~{y","!!#$'),/4::EEZYWWx~#$~!~{","!!#$&)-04;:FETZYVo~#'~#$~!~","!!#$&)-04<;GFM]ZYg~#)~#&~#$","!!#$&)+057<HGG^]Z^}~#)~#%x","!!#$&(+055<CHG`^ZVt~#,~#%x",
  "!!#$&(+-25=>IHX_ZVe~#.~#%x","!!#$&(+.16==JHP_ZVT{~#%x"]

def powers (r : ℕ) : List ℕ :=
  if r=0 then [] else KoalaSplitGateWords.powers (powersTape.getD (r-1) "")

def plainPowers : ℕ → List ℕ
  | _ => []

def tailPowers : List ℕ := KoalaSplitGateWords.powers "!!#$&)-/28@?MKMfb_Z~##~#:~#2~#*~!~vme]~#q~%=~%`"

def priced (r:ℕ):Bool:=rowCheck gate r (boxes r) (powers r) (plain r) (plainPowers r)
private theorem priced_list : (List.range 58).all (fun i => priced (i+1)) = true := by decide +kernel

theorem prices {r : ℕ} (hr : 0 < r) (hR : r < terminal) : priced r = true :=
  price hr hR priced_list

theorem tail:plainCheck gate terminal (4012,1650,550) tailPowers=true:=by decide +kernel

private abbrev Chunk (i n v : ℕ) := lossChunk 48 envelope plain boxes i n = v
private theorem checkPart (i n v : ℕ) (ok : Chunk i n v := by decide +kernel) : Chunk i n v := ok
private def part0 := checkPart 0 6 0x2384dc4cc14
private def part1 := checkPart 6 6 0x2384dc4cc14
private def part2 := checkPart 12 6 0x2384dc4cc14
private def part3 := checkPart 18 6 0x236a06124d3
private def part4 := checkPart 24 6 0x22ab1056905
private def part5 := checkPart 30 6 0x215e1e36d12
private def part6 := checkPart 36 6 0x1f2599f2cf1
private def part7 := checkPart 42 6 0x1bb7f3bb79a
private def part8 := checkPart 48 6 0x1677ee172d7
private def part9 := checkPart 54 4 0xb7784c1c97

theorem loss_bound (N : ℕ) : Bound envelope terminal plain boxes 20808791544607 N :=
  loss_of_chunks 48 envelope terminal plain boxes 20808791544607 N (by decide) (by decide)
    (LossSum.empty _ _ _ _
      |>.append 6 0x2384dc4cc14 part0 |>.append 6 0x2384dc4cc14 part1 |>.append 6 0x2384dc4cc14 part2 |>.append 6 0x236a06124d3 part3
      |>.append 6 0x22ab1056905 part4 |>.append 6 0x215e1e36d12 part5 |>.append 6 0x1f2599f2cf1 part6 |>.append 6 0x1bb7f3bb79a part7
      |>.append 6 0x1677ee172d7 part8 |>.append 4 0xb7784c1c97 part9)

def receipt : KoalaSplitProof.Receipt envelope split unit :=
  ⟨terminal, plain, boxes, powers, plainPowers, tailPowers, 20808791544607,
    by decide,by decide,loss_bound,fun _ h h' => prices h h', tail⟩

end KoalaAt2428Gate63

#print axioms KoalaAt2428Gate63.loss_bound
#print axioms KoalaAt2428Gate63.receipt
