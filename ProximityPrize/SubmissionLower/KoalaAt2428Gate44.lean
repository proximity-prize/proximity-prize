import ProximityPrize.SubmissionLower.KoalaGateSharedData
import ProximityPrize.SubmissionLower.KoalaGateChunkSums
import ProximityPrize.SubmissionLower.KoalaSplitGateWords

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000

set_option linter.defProp false

namespace KoalaAt2428Gate44
open KoalaGateSharedData
open FadicGate KoalaGateCheck
open KoalaWeightedRate (Envelope)
open KoalaFarBridge (rowCheck plainCheck)

def envelope : Envelope :=
  ⟨132,54,4,135,54,3432,4435,⟨7286865905,33635103245,71689325138⟩,3121833533016⟩
abbrev split:ℕ:=48
abbrev unit:ℕ:=1919967329280
abbrev terminal:ℕ:=65
abbrev gate:=KoalaSplitRow.rate envelope split unit

private def boxesTape : List (List Entry) := [
  b05o,b04x,b043,b035,b023,b027,b00y,bzv,
  bzx,byt,bxb,bxg,bvs,bvv,bu9,bua,
  bt0,bsy,bs2,bs1,brz,br0,bpz,bos,
  bnd,bln,bk2,bk5,bie,bifAtom,bfj,bfl,
  bbe,bbx,b59,b4u,b4w,b4y,b50,b51,
  b52,b53,b54,b55,b56,b57]
def boxes (r : ℕ) : List FadicGate.Entry :=
  if r < 19 then [] else boxesTape.getD (r-19) []

def plain : ℕ → ℕ × ℕ × ℕ
  | _ => (0,0,0)

private def powersTape : List String := [
  "","","","","","","","",
  "","","","","","","","",
  "","","","!#","!#%","!#&)","!#%).",z3O,
  "!#%(,5","!#%(,15","!#%(,06","!#%'-17D","!#$'*18>D","!#$(+298F","!#$'+.49GF","!#$'+.3:IG",
  "!#$'*/3;CII","!#$&*/4<=KI","!#$&*05=<LKW","!#$'*,58=NLO","!#$&)-15>HNLf","!#$&)-06?BON^","!#$&)-17@?QOU","!#$&).17A@SQOl",
  "!#$&(+28<ALSQdw","!#$&(+288BFTS[zw","!#$%(,/48CBVTTszw","!#$%),/39DCXVTk~!~zw","!##%(,/3:EDQXVb~#$~!~zw","!##%(*/4:@EKYXYy~#$~!~z","!##%(*04;;FE[YXq~#'~#$~!~z","!##%(+04<;GF][Yi~#*~#'~#$~!~",
  "!!#%'+-57<HGV][a~#!~#*~#'~#$|","!!#%'+-15<IHP_]Zw~#-~#*~#'~#$","!!#%')-15=DIJa_]o~#0~#-~#*~#'|","!!#%'*.16=?JIba_g~#)~#0~#-~#)~#'","!!#%'*.16>=KJ[ba`~!~~#4~#0~#-~#*|","!!#%'*.27?>LKUdbav~#7~#4~#0~#*|","!!#$'*,27;?MLOfddn~#/~#6~#6~#*|","!!#%'),287?HMLgfdc~#'~#:~#6~#*|",
  "!!#%&),/48@CNNbid_x~#@~#6~#*|","!!#$&),/38A@ONZid_h~#0~#6~#*|","!!#$&)-/39AAQNQid_Z}~#6~#*|","!!#$&)-/39CAQNKid_Zm~#6~#*|","!!#$&(+04:>AJNK`d_Z]~#%~#*|","!!#$&(+04:9ADNKUd_ZUr~#*|","!!#$&(+14:9A@NKLd_ZUb~#*|","!!#$&(,-469A@NKId_ZUQw|"]

def powers (r : ℕ) : List ℕ :=
  if r=0 then [] else KoalaSplitGateWords.powers (powersTape.getD (r-1) "")

def plainPowers : ℕ → List ℕ
  | _ => []

def tailPowers : List ℕ := KoalaSplitGateWords.powers "!!#$&),-149B@OLJ[a[WRl~#$vk`TI>3("

def priced (r:ℕ):Bool:=rowCheck gate r (boxes r) (powers r) (plain r) (plainPowers r)
private theorem priced_list : (List.range 64).all (fun i => priced (i+1)) = true := by decide +kernel

theorem prices {r : ℕ} (hr : 0 < r) (hR : r < terminal) : priced r = true :=
  price hr hR priced_list

theorem tail:plainCheck gate terminal (4012,1650,550) tailPowers=true:=by decide +kernel

private abbrev Chunk (i n v : ℕ) := lossChunk 16 envelope plain boxes i n = v
private theorem checkPart (i n v : ℕ) (ok : Chunk i n v := by decide +kernel) : Chunk i n v := ok
private def part0 := checkPart 0 6 0x2384dc4cc14
private def part1 := checkPart 6 6 0x2384dc4cc14
private def part2 := checkPart 12 6 0x2384dc4cc14
private def part3 := checkPart 18 6 0x2334d77f736
private def part4 := checkPart 24 6 0x225e7c11fdd
private def part5 := checkPart 30 6 0x20d6b94b901
private def part6 := checkPart 36 6 0x1e3faa6a852
private def part7 := checkPart 42 6 0x1a01b327085
private def part8 := checkPart 48 6 0x13d9c62f76b
private def part9 := checkPart 54 6 0xc64aba19ff
private def part10 := checkPart 60 4 0x4ce17c27b5

theorem loss_bound (N : ℕ) : Bound envelope terminal plain boxes 20772216014406 N :=
  loss_of_chunks 16 envelope terminal plain boxes 20772216014406 N (by decide) (by decide)
    (LossSum.empty _ _ _ _
      |>.append 6 0x2384dc4cc14 part0 |>.append 6 0x2384dc4cc14 part1 |>.append 6 0x2384dc4cc14 part2 |>.append 6 0x2334d77f736 part3
      |>.append 6 0x225e7c11fdd part4 |>.append 6 0x20d6b94b901 part5 |>.append 6 0x1e3faa6a852 part6 |>.append 6 0x1a01b327085 part7
      |>.append 6 0x13d9c62f76b part8 |>.append 6 0xc64aba19ff part9 |>.append 4 0x4ce17c27b5 part10)

def receipt : KoalaSplitProof.Receipt envelope split unit :=
  ⟨terminal, plain, boxes, powers, plainPowers, tailPowers, 20772216014406,
    by decide,by decide,loss_bound,fun _ h h' => prices h h', tail⟩

end KoalaAt2428Gate44

#print axioms KoalaAt2428Gate44.loss_bound
#print axioms KoalaAt2428Gate44.receipt
