import ProximityPrize.SubmissionLower.KoalaAt2428Gate31
import ProximityPrize.SubmissionLower.KoalaGateSharedData
import ProximityPrize.SubmissionLower.KoalaGateChunkSums
import ProximityPrize.SubmissionLower.KoalaSplitGateWords

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000

set_option linter.defProp false

namespace KoalaAt2428Gate33
open KoalaGateSharedData
open FadicGate KoalaGateCheck
open KoalaWeightedRate (Envelope)
open KoalaFarBridge (rowCheck plainCheck)

def envelope : Envelope :=
  ⟨124,56,2,127,56,3224,4427,⟨10203700943,50017829220,12963418421⟩,4081798792783⟩
abbrev split:ℕ:=48
abbrev unit:ℕ:=1919967782400
abbrev terminal:ℕ:=69
abbrev gate:=KoalaSplitRow.rate envelope split unit

private def boxesTape : List (List Entry) := [
  b05u,b050,b04t,b040,b037,unpack 5 0xe694383236faa46,b022,b010,
  b00w,bzz,bzi,by2,bxc,bwd,bvt.take 9++unpack 1 0x1c032207,bvs,
  buc.take 10++unpack 1 0x1b5633fb,bu9.take 10++unpack 1 0x1fb941fa,bt2.take 11++unpack 1 0x1a53100a,bt0.take 11++unpack 1 0x1eb61e09,bs6.take 11++unpack 2 0x4e5beec22167bd9,br2.take 12++unpack 2 0x4b0f9ca1db2fa18,bpw.take 12++unpack 3 0x48c993a4cd567421133aff,boq.take 12++unpack 4 0x48c993a494954a4e9c6e82520217b,
  bnw,bn5.take 13++unpack 4 0x24a4aa56f4d5665a24c95af1,bll.take 13++unpack 5 0x1283060b7bf4f5d2c2292c85c8,bmo,bk3.take 14++unpack 5 0x12a40759fbf4d5625a2829368b,bk2.take 14++unpack 5 0xfdfbf4e9c6d22b89a2be,big.take 14++unpack 6 0x12f508b1fbf4b90dbc4e1b2f42f965dee,bie.take 15++unpack 5 0x25062c23f498a9344cd525c2b32dc2e,
  bfm.take 15++unpack 6 0x13460a09fa4c549a6f4f1bed62f95ea2c,bh0,bcz,bdi,b5o.take 17++unpack 6 0x288ef5523e62e224644ac3f4b50db42d397acf,b59.take 18++unpack 5 0x334450dc8488819e49ca5322b32bf3e,b7y,b5r,
  b5s,b24,b2b,b2j,b0y,b0z,b10,b11,
  b12,b13,b15,b14,b16]
def boxes (r : ℕ) : List FadicGate.Entry :=
  if r < 16 then [] else boxesTape.getD (r-16) []

def plain : ℕ → ℕ × ℕ × ℕ
  | _ => (0,0,0)

private def powersTape : List String := [
  "","","","","","","","",
  "","","","","","","","",
  "!#","!#","!#&","!#&+","!#&+/",z3r,z2Q,"!#%*07",
  "!#%(-8>","!#%)-38E","!#%).29GF",z58,"!#%(+3;CIW","!#%(,4<=KN","!#$',07<MK","!#$',05=OM_",
  "!#$'*05>IOV","!#$'+16?BQOo","!#$'+17@?RQg","!#$'+-7<@TR_~#!","!#$&).37BNTUw~#!",z6X,"!#$&*.29DCXVf~#*~#&~#!","!#$&*/39EDZX^~!~~#*~#&~#!",
  "!#$&),3:@ETZXv~#-~#*~#&","!#$&),4;;FN]Zn~#1~#-~#*~##","!#$&)-07;GG_]f~#)~#1~#-~#*",z51,z5O,"!#$%(+15=DISb`m~#1~#9~#5~#1~##","!##%(+16>?JMdbf~#(~#=~#9~#5~#/","!##%(+16>>KJfdb}~#A~#=~#9~#5~##",
  "!!#%',.7:>LK`fdu~#8~#A~#=~#9~#/","!!#%(,.37?MLYhfm~#0~#D~#A~#=~#9~##","!!#%(*/27@HMRihf~#(~#H~#D~#A~#=~#/","!!#%(*/28@DOMkih}~#@~#H~#D~#A~#:~##","!!#%'*/38A@POekiu~#8~#L~#H~#D~#;~#-","!!#%'+/39BAQP_mkj~#0~#P~#L~#F~#;~#-","!!#%'+-39>BRQXomj~#&~#H~#P~#H~#;~#-","!!#%')-4:9BMRQqnjr~#=~#S~#H~#;~#-",
  "!!#%')-16:CHSQjoje~#,~#U~#H~#;~#-}","!!#$'*-04:DCSQaojew~#C~#H~#;~#-}","!!#%'*.04;DCTQWojee~#1~#H~#;~#-}","!!#%'*.15;ECTQNoje`|~#H~#;~#-}","!!#$&),15;@CMQNfje`i~#6~#;~#-}","!!#$&),15;;CGQN[je`Z~#$~#;~#-}","!!#$&),15;:CBQNRje`Zn~#;~#-}","!!#$&),.57:CBQNLje`Z[~#(~#-}",
  "!!#$&),.24:CBQNLae`ZUs~#-}","!!#$&(,.14:CBKNLVe`ZUa~#-}","!!#$&(*.14:>BDNLLe`ZUOx}","!!#$&(*.14:9B@NLIe`ZUOf}"]

def powers (r : ℕ) : List ℕ :=
  if r=0 then [] else KoalaSplitGateWords.powers (powersTape.getD (r-1) "")

def plainPowers : ℕ → List ℕ
  | _ => []

def tailPowers : List ℕ := KoalaSplitGateWords.powers "!!#$&(*.15:9B@OLJ]b]WQX~#&vi[NA4"

def priced (r:ℕ):Bool:=rowCheck gate r (boxes r) (powers r) (plain r) (plainPowers r)
private theorem priced_list : (List.range 68).all (fun i => priced (i+1)) = true := by decide +kernel

theorem prices {r : ℕ} (hr : 0 < r) (hR : r < terminal) : priced r = true :=
  price hr hR priced_list

theorem tail:plainCheck gate terminal (4012,1650,550) tailPowers=true:=by decide +kernel

private abbrev Chunk (i n v : ℕ) := lossChunk 12 envelope plain boxes i n = v
private theorem checkPart (i n v : ℕ) (ok : Chunk i n v := by decide +kernel) : Chunk i n v := ok
private def part0 := checkPart 0 6 0x2384dc4cc14
private def part1 := checkPart 6 6 0x2384dc4cc14
private def part2 := checkPart 12 6 0x237a614343b
private def part3 := checkPart 18 6 0x231f18a84bf
private def part4 := checkPart 24 6 0x224a2fd74ac
private def part5 := checkPart 30 6 0x20c446fbe80
private def part6 := checkPart 36 6 0x1e0a8c8485c
private def part7 := checkPart 42 6 0x19cfd4cf9cc
private def part8 := checkPart 48 6 0x1392f090ebb
private def part9 := checkPart 54 6 0xc107a280a2
private def part10 := checkPart 60 6 0x614a4e5682
private def part11 := checkPart 66 2 0x11e2b422f9

theorem loss_bound (N : ℕ) : Bound envelope terminal plain boxes 20848381054798 N :=
  loss_of_chunks 12 envelope terminal plain boxes 20848381054798 N (by decide) (by decide)
    (LossSum.empty _ _ _ _
      |>.append 6 0x2384dc4cc14 part0 |>.append 6 0x2384dc4cc14 part1 |>.append 6 0x237a614343b part2 |>.append 6 0x231f18a84bf part3
      |>.append 6 0x224a2fd74ac part4 |>.append 6 0x20c446fbe80 part5 |>.append 6 0x1e0a8c8485c part6 |>.append 6 0x19cfd4cf9cc part7
      |>.append 6 0x1392f090ebb part8 |>.append 6 0xc107a280a2 part9 |>.append 6 0x614a4e5682 part10 |>.append 2 0x11e2b422f9 part11)

def receipt : KoalaSplitProof.Receipt envelope split unit :=
  ⟨terminal, plain, boxes, powers, plainPowers, tailPowers, 20848381054798,
    by decide,by decide,loss_bound,fun _ h h' => prices h h', tail⟩

end KoalaAt2428Gate33

#print axioms KoalaAt2428Gate33.loss_bound
#print axioms KoalaAt2428Gate33.receipt
