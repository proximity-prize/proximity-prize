import ProximityPrize.SubmissionLower.KoalaAt2428Gate33
import ProximityPrize.SubmissionLower.KoalaGateSharedData
import ProximityPrize.SubmissionLower.KoalaGateChunkSums
import ProximityPrize.SubmissionLower.KoalaSplitGateWords

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000

set_option linter.defProp false

namespace KoalaAt2428Gate34
open KoalaGateSharedData
open FadicGate KoalaGateCheck
open KoalaWeightedRate (Envelope)
open KoalaFarBridge (rowCheck plainCheck)

def envelope : Envelope :=
  ⟨136,54,12,137,54,3536,4437,⟨9168554006,52922312712,9889325065⟩,4061925144403⟩
abbrev split:ℕ:=48
abbrev unit:ℕ:=1919968440960
abbrev terminal:ℕ:=68
abbrev gate:=KoalaSplitRow.rate envelope split unit

private def boxesTape : List (List Entry) := [
  b05l,b04u,b03z,b033,b022,b023,b00w,bzz,
  bzv,bys,bxc,bxb,bvt,bvs,buc,bu9,
  bt2,bt0,bsy,bs2,bqz,bpu,bol,bn5,
  bls,blk,bk3.take 18++unpack 1 0x1aa93787,bk2,big.take 19++unpack 1 0x1aa93787,bij,bfm.take 20++unpack 1 0x1aa93787,bfj.take 20++unpack 1 0x1f630bfe,
  bbb.take 21++unpack 1 0x1aa93787,bbc.take 21++unpack 1 0x200fbffb,b5o.take 22++unpack 1 0x1b5616d5,b4s,b4t,b4v,b4x,b4z,
  b4l,b4m,b4n,b4o,b4p,b4q,b4r,b58,
  b5m,b5l]
def boxes (r : ℕ) : List FadicGate.Entry :=
  if r < 18 then [] else boxesTape.getD (r-18) []

def plain : ℕ → ℕ × ℕ × ℕ
  | _ => (0,0,0)

private def powersTape : List String := [
  "","","","","","","","",
  "","","","","","","","",
  "","","!#","!#&","!#&+",z3r,"!#%)0","!#%*07",
  "!#%(-8=",z41,"!#%)-29G",z58,z6a,"!#%(,4<<KN","!#$',07<LK","!#$',/4=NL_",
  "!#$'*05>HNU","!#$'*06?BPNo","!#$'+16@?RPf","!#$'+-7;@TR^","!#$&).37ANTTv","!#$&*.28BGUTn~#%","!#$&*.29CBWUf~#)~#%","!#$&*/39DCYW]~!~~#)~#%",
  "!#$&),3:@DSYWu~#-~#)~#%","!#$&),4;:FM[Ym~#0~#-~#)~##","!#$&)-06;GF^[e~#(~#0~#-~#)","!#$&)-04;HG`^[}~#4~#0~#-~##","!#$&(-05<IHY`^u~#8~#4~#0~#-",z4u,"!##%(+16=?JLcbd~#(~#<~#8~#4~#/","!##%(+16>=KJecb|~#@~#<~#8~#4~##",
  "!!#%',.7:>LK_ect~#7~#@~#<~#8~#/","!!#%(,.37?MLXgel~#/~#C~#@~#<~#8~##","!!#%(*.27?HMRige~#'~#G~#C~#@~#;~#/","!!#%(*/28@CNMkig|~#?~#G~#C~#>~#9~##","!!#%'*/38A@ONekis~#7~#K~#G~#A~#:~#-","!!#%'+/39BAPO^mkh~#.~#O~#J~#E~#:~#-","!!#%'+-39=BQPWnmj~#%~#E~#M~#G~#:~#-","!!#%')-4:9BLQQpnjq~#<~#Q~#G~#:~#-",
  "!!#%')-16:CGRQjoje~#+~#T~#G~#:~#-","!!#$'*-04:DCSQaojev~#B~#G~#:~#-","!!#%'*-04:DCTQVojed~#0~#G~#:~#-","!!#%'*.15;ECTQNoje_{~#G~#:~#-","!!#$&),15;@CMQNeje_i~#5~#:~#-","!!#$&),15;;CFQN[je_Y~##~#:~#-","!!#$&),15;:CAQNQje_Yn~#:~#-","!!#$&),.57:CAQNKje_YZ~#(~#-",
  "!!#$&),.24:CAQNK`e_YTs~#-","!!#$&(,.14:CAJNKUe_YT`~#-","!!#$&(*.14:>ADNKLe_YTOx"]

def powers (r : ℕ) : List ℕ :=
  if r=0 then [] else KoalaSplitGateWords.powers (powersTape.getD (r-1) "")

def plainPowers : ℕ → List ℕ
  | _ => []

def tailPowers : List ℕ := KoalaSplitGateWords.powers "!!#$&(*.14:9B@OLIfa[VQj~#$tgYL@3"

def priced (r:ℕ):Bool:=rowCheck gate r (boxes r) (powers r) (plain r) (plainPowers r)
private theorem priced_list : (List.range 67).all (fun i => priced (i+1)) = true := by decide +kernel

theorem prices {r : ℕ} (hr : 0 < r) (hR : r < terminal) : priced r = true :=
  price hr hR priced_list

theorem tail:plainCheck gate terminal (4012,1650,550) tailPowers=true:=by decide +kernel

private abbrev Chunk (i n v : ℕ) := lossChunk 12 envelope plain boxes i n = v
private theorem checkPart (i n v : ℕ) (ok : Chunk i n v := by decide +kernel) : Chunk i n v := ok
private def part0 := checkPart 0 6 0x2384dc4cc14
private def part1 := checkPart 6 6 0x2384dc4cc14
private def part2 := checkPart 12 6 0x238243abf83
private def part3 := checkPart 18 6 0x23271c522fa
private def part4 := checkPart 24 6 0x224f711d919
private def part5 := checkPart 30 6 0x20c4f152377
private def part6 := checkPart 36 6 0x1e0f1abed43
private def part7 := checkPart 42 6 0x19c9101659b
private def part8 := checkPart 48 6 0x1388608f413
private def part9 := checkPart 54 6 0xbf58cc26c8
private def part10 := checkPart 60 6 0x5e5a3117d8
private def part11 := checkPart 66 1 0x90c6a8d99

theorem loss_bound (N : ℕ) : Bound envelope terminal plain boxes 20793007180383 N :=
  loss_of_chunks 12 envelope terminal plain boxes 20793007180383 N (by decide) (by decide)
    (LossSum.empty _ _ _ _
      |>.append 6 0x2384dc4cc14 part0 |>.append 6 0x2384dc4cc14 part1 |>.append 6 0x238243abf83 part2 |>.append 6 0x23271c522fa part3
      |>.append 6 0x224f711d919 part4 |>.append 6 0x20c4f152377 part5 |>.append 6 0x1e0f1abed43 part6 |>.append 6 0x19c9101659b part7
      |>.append 6 0x1388608f413 part8 |>.append 6 0xbf58cc26c8 part9 |>.append 6 0x5e5a3117d8 part10 |>.append 1 0x90c6a8d99 part11)

def receipt : KoalaSplitProof.Receipt envelope split unit :=
  ⟨terminal, plain, boxes, powers, plainPowers, tailPowers, 20793007180383,
    by decide,by decide,loss_bound,fun _ h h' => prices h h', tail⟩

end KoalaAt2428Gate34

#print axioms KoalaAt2428Gate34.loss_bound
#print axioms KoalaAt2428Gate34.receipt
