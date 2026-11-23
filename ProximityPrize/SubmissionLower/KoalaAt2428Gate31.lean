import ProximityPrize.SubmissionLower.KoalaAt2428Gate30
import ProximityPrize.SubmissionLower.KoalaGateSharedData
import ProximityPrize.SubmissionLower.KoalaGateChunkSums
import ProximityPrize.SubmissionLower.KoalaSplitGateWords

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000

set_option linter.defProp false

namespace KoalaAt2428Gate31
open KoalaGateSharedData
open FadicGate KoalaGateCheck
open KoalaWeightedRate (Envelope)
open KoalaFarBridge (rowCheck plainCheck)

def envelope : Envelope :=
  ⟨132,55,8,135,55,3432,4435,⟨9287875425,47223230793,31919852720⟩,4009390081058⟩
abbrev split:ℕ:=48
abbrev unit:ℕ:=1919967715200
abbrev terminal:ℕ:=70
abbrev gate:=KoalaSplitRow.rate envelope split unit

private def boxesTape : List (List Entry) := [
  b05k,b04t,b040,b037,b033,b022,b010,b00w,
  bzz,bzv,bys,bxc,bxb,bvt,bvs,buc,
  bu9,bt2,bt0,bs6,br2,bpw,boq,bnw.take 13++unpack 4 0x490a144494954a4b105c020bccb18,
  bn5,bll.take 17++unpack 1 0x19fcda18,bmo.take 14++unpack 4 0x37bf4b501d4241c89da,bk3.take 18++unpack 1 0x1a52f323,bk2,big.take 19++unpack 1 0x1a52f323,bie.take 19++unpack 1 0x1eb657ec,bfm.take 20++unpack 1 0x1a52f323,
  bh0.take 16++unpack 5 0x2567af724a50956f4b105cc2a2ff20f,bcz.take 16++unpack 6 0x274df6924a50956f49095644d5723c2e93000e,bdi.take 17++unpack 5 0x1304e8a37a484ab23f292ca2d2,b5p.take 21++unpack 2 0x50a1a3c2622a5bb,b4s.take 16++unpack 7 0x4d54a16448c60448881ec49ca5324cd62544f5d6863bbc384f,b4u,b4w,b4y,
  b50,b51,b52,b53,b54,b55,b56,b57,
  b5k,b5n,b64,b4a.take 23,b4e.take 23]
def boxes (r : ℕ) : List FadicGate.Entry :=
  if r < 17 then [] else boxesTape.getD (r-17) []

def plain : ℕ → ℕ × ℕ × ℕ
  | _ => (0,0,0)

private def powersTape : List String := [
  "","","","","","","","",
  "","","","","","","","",
  "","!#","!#&","!#&+","!#&+",z3r,z2Q,"!#%*07",
  "!#%(-8=",z41,"!#%).29G",z58,z6a,"!#%(,4<=KO","!#$',07<MK","!#$',05=OM_",
  "!#$'*05>IOV","!#$'+16?BQOo","!#$'+17A?RQg","!#$'+.7<ATR_~#!","!#$&).37BNTUw~#!",z6X,"!#$&*/39DCXVf~#)~#&~#!","!#$&*/39EDZX^~!~~#)~#&~#!",
  "!#$&),3:@ETZXv~#-~#)~#&","!#$&),4;;FN]Zn~#1~#-~#)~##","!#$&)-07;GG_]f~#)~#1~#-~#)",z51,z5O,"!#$%(+15=DISb`n~#1~#9~#5~#1~##","!##%(+16>?JMdbf~#)~#<~#9~#5~#/","!##%(+16>>KJfdb~!~~#@~#<~#9~#5~##",
  "!!#%',.7:>LK`fdu~#8~#@~#<~#9~#/","!!#%(,.37?NLYhfm~#0~#D~#@~#<~#9~##","!!#%(*/27@INSjhf~#(~#H~#D~#@~#<~#/","!!#%(*/28@DONkjh}~#@~#H~#D~#@~#;~##","!!#%'*/38A@POekju~#8~#L~#H~#C~#=~#/","!!#%'+/39BAQP_mkk~#0~#P~#L~#G~#=~#0","!!#%'+-49>BRQXonl~#'~#G~#O~#J~#=~#0","!!#%')-4::CMRRqolu~#?~#S~#J~#=~#0",
  "!!#%'*-16:CHSRkqlf~#/~#W~#J~#=~#0","!!#%'*-04:DCTRcqlfz~#F~#J~#=~#0","!!#%'*.05;EDURXqlfh~#4~#J~#=~#0","!!#%'*.15;FDUROqlfa~#!~#J~#=~#0","!!#$&),15<ADNROglfam~#8~#=~#0","!!#$&),16<;DHRO^lfa[~#&~#=~#0","!!#$&),26<;DBROSlfa[q~#=~#0","!!#$&),.68;DBROLlfa[_~#+~#0",
  "!!#$&),.25;DBROLbfa[Vv~#0","!!#$&(,.15;DBKOLWfa[Vd~#0","!!#$&(*.15;?BEOLNfa[VQ{","!!#$&(*.15;:B@OLJfa[VQi","!!#$&(*.15;9B@OLJ]a[VQV"]

def powers (r : ℕ) : List ℕ :=
  if r=0 then [] else KoalaSplitGateWords.powers (powersTape.getD (r-1) "")

def plainPowers : ℕ → List ℕ
  | _ => []

def tailPowers : List ℕ := KoalaSplitGateWords.powers "!!#$&(*.15;9BAOMJSb]VQLotgYL>1$"

def priced (r:ℕ):Bool:=rowCheck gate r (boxes r) (powers r) (plain r) (plainPowers r)
private theorem priced_list : (List.range 69).all (fun i => priced (i+1)) = true := by decide +kernel

theorem prices {r : ℕ} (hr : 0 < r) (hR : r < terminal) : priced r = true :=
  price hr hR priced_list

theorem tail:plainCheck gate terminal (4012,1650,550) tailPowers=true:=by decide +kernel

private abbrev Chunk (i n v : ℕ) := lossChunk 12 envelope plain boxes i n = v
private theorem checkPart (i n v : ℕ) (ok : Chunk i n v := by decide +kernel) : Chunk i n v := ok
private def part0 := checkPart 0 6 0x2384dc4cc14
private def part1 := checkPart 6 6 0x2384dc4cc14
private def part2 := checkPart 12 6 0x237deb2d94f
private def part3 := checkPart 18 6 0x2320a22a499
private def part4 := checkPart 24 6 0x224e9db955c
private def part5 := checkPart 30 6 0x20c0eeef118
private def part6 := checkPart 36 6 0x1e03143ab5a
private def part7 := checkPart 42 6 0x19c22f1165c
private def part8 := checkPart 48 6 0x137bfa68205
private def part9 := checkPart 54 6 0xbdba4c34eb
private def part10 := checkPart 60 6 0x5c00c6738e
private def part11 := checkPart 66 3 0x15f10ffff1

theorem loss_bound (N : ℕ) : Bound envelope terminal plain boxes 20818732484777 N :=
  loss_of_chunks 12 envelope terminal plain boxes 20818732484777 N (by decide) (by decide)
    (LossSum.empty _ _ _ _
      |>.append 6 0x2384dc4cc14 part0 |>.append 6 0x2384dc4cc14 part1 |>.append 6 0x237deb2d94f part2 |>.append 6 0x2320a22a499 part3
      |>.append 6 0x224e9db955c part4 |>.append 6 0x20c0eeef118 part5 |>.append 6 0x1e03143ab5a part6 |>.append 6 0x19c22f1165c part7
      |>.append 6 0x137bfa68205 part8 |>.append 6 0xbdba4c34eb part9 |>.append 6 0x5c00c6738e part10 |>.append 3 0x15f10ffff1 part11)

def receipt : KoalaSplitProof.Receipt envelope split unit :=
  ⟨terminal, plain, boxes, powers, plainPowers, tailPowers, 20818732484777,
    by decide,by decide,loss_bound,fun _ h h' => prices h h', tail⟩

end KoalaAt2428Gate31

#print axioms KoalaAt2428Gate31.loss_bound
#print axioms KoalaAt2428Gate31.receipt
