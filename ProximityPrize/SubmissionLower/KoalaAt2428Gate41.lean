import ProximityPrize.SubmissionLower.KoalaGateSharedData
import ProximityPrize.SubmissionLower.KoalaGateChunkSums
import ProximityPrize.SubmissionLower.KoalaSplitGateWords

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000

set_option linter.defProp false

namespace KoalaAt2428Gate41
open KoalaGateSharedData
open FadicGate KoalaGateCheck
open KoalaWeightedRate (Envelope)
open KoalaFarBridge (rowCheck plainCheck)

def envelope : Envelope :=
  ⟨136,56,2,137,56,3536,4437,⟨4101076446,15896729047,151338023608⟩,1702949083300⟩
abbrev split:ℕ:=48
abbrev unit:ℕ:=1919966323200
abbrev terminal:ℕ:=66
abbrev gate:=KoalaSplitRow.rate envelope split unit

private def boxesTape : List (List Entry) := [
  b05p,b04y,b044,b038,b036,b025,b011,bzx,
  bzy,byu,byp,bxj,bvv,bu9,bua,bub,
  bsy,bsz,bs1,brz,br0,bqx,bq0,bot,
  bne,blp,bk5,bie,bifAtom,bfj,bfl,bbc,
  bc4,b7e.take 22,b7v.take 22,b85.take 22,b8j.take 22,b8q.take 22,b93.take 22,b99.take 22,
  b9m.take 22,b9r.take 22,ba4.take 22,baa.take 22,bak.take 22,baq.take 22]
def boxes (r : ℕ) : List FadicGate.Entry :=
  if r < 20 then [] else boxesTape.getD (r-20) []

def plain : ℕ → ℕ × ℕ × ℕ
  | _ => (0,0,0)

private def powersTape : List String := [
  "","","","","","","","",
  "","","","","","","","",
  "","","","","!#","!#%","!#%)","!#%)",
  "!#%(+","!#%(+/","!#$(,/5","!#%',06","!#$'*07;","!#$'*187","!#$'+-38D","!#$'+.29ED",
  "!#$').29?EC","!#$&).3:9FE","!#$&*/3;:HF","!#$&*,46;JHE","!#$&(,04<CJH","!#$&)-05=>KJQ","!#$&)-05>=LKJ","!#$%)-16?>NLK^",
  "!#$&(+17:?HNLW","!#$&(+177@BONPk","!#$%(+.37A@QOMdk","!#$%(,.28AARQO]nk","!##%',.28BALRQTpnk","!##%'*/39>BGTROipnk","!##%(*/399CBUTRbspnk","!##%(*/4:9DCVUTZuspn",
  "!!#%'*,46:EDQVUSnuspm","!!#%'+-04;FEKXVUgxusp","!!#%')-04;AFEZXVa{xusl","!!#%')-05<<GF[ZXYt{xus","!!#%&)-15<<HGU[ZWm~!~zxw","!!#%'*.16=<IHP^[Zf~##~!~{w","!!#$'*+169=JIJ`_`_y~##~#$w","!!#$'),266>EJJa``Zs~#&~#$w",
  "!!#$&),.37?AKL[d`Zk~#.~#$w","!!#$&),.27??LLVd`Z]}~#$w","!!#$&),/28@AOLNd`ZVo~#$w","!!#$&),/38BAOLJd`ZVa~#$w","!!#$&(+/3:=AILJ[`ZVRsw","!!#$&(+04:9ACLJR`ZVQew","!!#$&(+14:9A?LJJ`ZVQVw","!!#$&(,-469A?LJG`ZVQMi",
  "!!#$&),-139A?LJGVZVQM["]

def powers (r : ℕ) : List ℕ :=
  if r=0 then [] else KoalaSplitGateWords.powers (powersTape.getD (r-1) "")

def plainPowers : ℕ → List ℕ
  | _ => []

def tailPowers : List ℕ := KoalaSplitGateWords.powers "!!#$&(,-039A?FJGNZVQMMndYOE;1'"

def priced (r:ℕ):Bool:=rowCheck gate r (boxes r) (powers r) (plain r) (plainPowers r)
private theorem priced_list : (List.range 65).all (fun i => priced (i+1)) = true := by decide +kernel

theorem prices {r : ℕ} (hr : 0 < r) (hR : r < terminal) : priced r = true :=
  price hr hR priced_list

theorem tail:plainCheck gate terminal (4012,1650,550) tailPowers=true:=by decide +kernel

private abbrev Chunk (i n v : ℕ) := lossChunk 24 envelope plain boxes i n = v
private theorem checkPart (i n v : ℕ) (ok : Chunk i n v := by decide +kernel) : Chunk i n v := ok
private def part0 := checkPart 0 6 0x2384dc4cc14
private def part1 := checkPart 6 6 0x2384dc4cc14
private def part2 := checkPart 12 6 0x2384dc4cc14
private def part3 := checkPart 18 6 0x2345d5b8aba
private def part4 := checkPart 24 6 0x2268c1ef8c0
private def part5 := checkPart 30 6 0x20d360f3261
private def part6 := checkPart 36 6 0x1e350564bf4
private def part7 := checkPart 42 6 0x19e6750e4d0
private def part8 := checkPart 48 6 0x13a64ca6293
private def part9 := checkPart 54 6 0xc4e0ecdbaa
private def part10 := checkPart 60 5 0x5b1203eff4

theorem loss_bound (N : ℕ) : Bound envelope terminal plain boxes 20809523034380 N :=
  loss_of_chunks 24 envelope terminal plain boxes 20809523034380 N (by decide) (by decide)
    (LossSum.empty _ _ _ _
      |>.append 6 0x2384dc4cc14 part0 |>.append 6 0x2384dc4cc14 part1 |>.append 6 0x2384dc4cc14 part2 |>.append 6 0x2345d5b8aba part3
      |>.append 6 0x2268c1ef8c0 part4 |>.append 6 0x20d360f3261 part5 |>.append 6 0x1e350564bf4 part6 |>.append 6 0x19e6750e4d0 part7
      |>.append 6 0x13a64ca6293 part8 |>.append 6 0xc4e0ecdbaa part9 |>.append 5 0x5b1203eff4 part10)

def receipt : KoalaSplitProof.Receipt envelope split unit :=
  ⟨terminal, plain, boxes, powers, plainPowers, tailPowers, 20809523034380,
    by decide,by decide,loss_bound,fun _ h h' => prices h h', tail⟩

end KoalaAt2428Gate41

#print axioms KoalaAt2428Gate41.loss_bound
#print axioms KoalaAt2428Gate41.receipt
