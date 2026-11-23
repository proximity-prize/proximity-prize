import ProximityPrize.SubmissionLower.KoalaAt2428Gate34
import ProximityPrize.SubmissionLower.KoalaGateSharedData
import ProximityPrize.SubmissionLower.KoalaGateChunkSums
import ProximityPrize.SubmissionLower.KoalaSplitGateWords

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000

set_option linter.defProp false

namespace KoalaAt2428Gate36
open KoalaGateSharedData
open FadicGate KoalaGateCheck
open KoalaWeightedRate (Envelope)
open KoalaFarBridge (rowCheck plainCheck)

def envelope : Envelope :=
  ⟨128,55,2,131,55,3328,4431,⟨9673770763,51011410231,12190570593⟩,4039720872391⟩
abbrev split:ℕ:=48
abbrev unit:ℕ:=1919967567360
abbrev terminal:ℕ:=68
abbrev gate:=KoalaSplitRow.rate envelope split unit

private def boxesTape : List (List Entry) := [
  b05k,b04t,b040,b037,b033,b022,b010,b00w,
  bzz,bzv,bys,bxc,bxb,bvt,bvs,buc,
  bu9,bt2,bt0,bs6,br2,bpw,boq,bnc,
  bn5,bls,blk,bk3.take 18++unpack 1 0x1aa95473,bk2,big.take 19++unpack 1 0x1aa95473,bij,bfm.take 20++unpack 1 0x1aa95473,
  bfj.take 20++unpack 1 0x1fb95062,bbb.take 21++unpack 1 0x1aa95473,bbe.take 21++unpack 1 0x1fb95062,b70,b5q.take 22++unpack 1 0x261f6d9e,b5c,b5d,b5e,
  b5f,b5g,b5h,b5i,b5a,b5b,b5j,b5t,
  b61,b40.take 5++unpack 18 0x4b5ebe5af5f2d7af96bd7cb5ebe5af90129d5f,b3u.take 4++unpack 20 0xbe5af5f2d7af96bd7cb5ebe5af5f2d7af96258367]
def boxes (r : ℕ) : List FadicGate.Entry :=
  if r < 17 then [] else boxesTape.getD (r-17) []

def plain : ℕ → ℕ × ℕ × ℕ
  | _ => (0,0,0)

private def powersTape : List String := [
  "","","","","","","","",
  "","","","","","","","",
  "","!#","!#&","!#&+","!#&+",z3r,"!#%)06","!#%*07",
  "!#%(-8=",z41,"!#%).29G",z58,z6a,"!#%(,4<<KN","!#$',07<LK","!#$',/4=NL_",
  "!#$'*05>HNU","!#$'*06?BPNn","!#$'+16@?RPf","!#$'+-7;@TR^~!~","!#$&).37ANTTv~!~","!#$&*.28BGVTn~#%~!~","!#$&*.29CBWVf~#)~#%~!~","!#$&*/39ECYW]}~#)~#%~!~",
  "!#$&),3:@ESYWu~#,~#)~#%","!#$&),4;;FM[Ym~#0~#,~#)~##","!#$&)-07;GF^[e~#(~#0~#,~#)","!#$&)-04;HG`^[}~#4~#0~#,~##","!#$&(-05<IHY`^u~#8~#4~#0~#,","!#$%(+05=DIRb`m~#0~#8~#4~#0~##","!##%(+16=?JLcbd~#'~#<~#8~#4~#/","!##%(+16>=KJecb|~#?~#<~#8~#4~##",
  "!!#%',.7:>LK_ect~#7~#?~#<~#8~#/","!!#%(,.37?MLXgel~#/~#C~#?~#<~#8~##","!!#%(*.27?HMRige~#'~#G~#C~#?~#<~#/","!!#%(*/28@CNMkig|~#?~#G~#C~#?~#;~##","!!#%'*/38A@ONekis~#7~#K~#G~#C~#=~#/","!!#%'+/39BAPO^mki~#.~#O~#K~#G~#=~#0","!!#%'+-39=BQPWnmk~#&~#F~#O~#I~#=~#0","!!#%')-4:9BLQQpnks~#>~#R~#I~#=~#0",
  "!!#%')-16:CGRQjpkf~#-~#V~#I~#=~#0","!!#$'*-04:DCSQapkfx~#D~#I~#=~#0","!!#%'*-04:DCTQWpkff~#2~#I~#=~#0","!!#%'*.15;ECTQOpkf`}~#I~#=~#0","!!#$&),15;@CMQOfkf`k~#7~#=~#0","!!#$&),15;;CGQO[kf`Z~#%~#=~#0","!!#$&),15;:CBQORkf`Zp~#=~#0","!!#$&),.57:CBQOLkf`Z^~#*~#0",
  "!!#$&),.24:CBQOLaf`ZUu~#0","!!#$&(,.14:CBKOLVf`ZUc~#0","!!#$&(*.14:>BDOLMf`ZUP{~##"]

def powers (r : ℕ) : List ℕ :=
  if r=0 then [] else KoalaSplitGateWords.powers (powersTape.getD (r-1) "")

def plainPowers : ℕ → List ℕ
  | _ => []

def tailPowers : List ℕ := KoalaSplitGateWords.powers "!!#$&(*.14:9B@OLIfa[VQk~#%ui[NA4("

def priced (r:ℕ):Bool:=rowCheck gate r (boxes r) (powers r) (plain r) (plainPowers r)
private theorem priced_list : (List.range 67).all (fun i => priced (i+1)) = true := by decide +kernel

theorem prices {r : ℕ} (hr : 0 < r) (hR : r < terminal) : priced r = true :=
  price hr hR priced_list

theorem tail:plainCheck gate terminal (4012,1650,550) tailPowers=true:=by decide +kernel

private abbrev Chunk (i n v : ℕ) := lossChunk 12 envelope plain boxes i n = v
private theorem checkPart (i n v : ℕ) (ok : Chunk i n v := by decide +kernel) : Chunk i n v := ok
private def part0 := checkPart 0 6 0x2384dc4cc14
private def part1 := checkPart 6 6 0x2384dc4cc14
private def part2 := checkPart 12 6 0x237df89fdbf
private def part3 := checkPart 18 6 0x23216b9168c
private def part4 := checkPart 24 6 0x22513487c89
private def part5 := checkPart 30 6 0x20c71ba8eeb
private def part6 := checkPart 36 6 0x1e0fad07a55
private def part7 := checkPart 42 6 0x19d8d6b55f9
private def part8 := checkPart 48 6 0x13a10ec31b0
private def part9 := checkPart 54 6 0xc0ba8f9da5
private def part10 := checkPart 60 6 0x5f2a843577
private def part11 := checkPart 66 1 0x907d7b48a

theorem loss_bound (N : ℕ) : Bound envelope terminal plain boxes 20811748688267 N :=
  loss_of_chunks 12 envelope terminal plain boxes 20811748688267 N (by decide) (by decide)
    (LossSum.empty _ _ _ _
      |>.append 6 0x2384dc4cc14 part0 |>.append 6 0x2384dc4cc14 part1 |>.append 6 0x237df89fdbf part2 |>.append 6 0x23216b9168c part3
      |>.append 6 0x22513487c89 part4 |>.append 6 0x20c71ba8eeb part5 |>.append 6 0x1e0fad07a55 part6 |>.append 6 0x19d8d6b55f9 part7
      |>.append 6 0x13a10ec31b0 part8 |>.append 6 0xc0ba8f9da5 part9 |>.append 6 0x5f2a843577 part10 |>.append 1 0x907d7b48a part11)

def receipt : KoalaSplitProof.Receipt envelope split unit :=
  ⟨terminal, plain, boxes, powers, plainPowers, tailPowers, 20811748688267,
    by decide,by decide,loss_bound,fun _ h h' => prices h h', tail⟩

end KoalaAt2428Gate36

#print axioms KoalaAt2428Gate36.loss_bound
#print axioms KoalaAt2428Gate36.receipt
