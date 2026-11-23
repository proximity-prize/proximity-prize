import ProximityPrize.SubmissionLower.KoalaAt2428Gate19
import ProximityPrize.SubmissionLower.KoalaGateSharedData
import ProximityPrize.SubmissionLower.KoalaGateChunkSums
import ProximityPrize.SubmissionLower.KoalaSplitGateWords

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000

set_option linter.defProp false

namespace KoalaAt2428Gate20
open KoalaGateSharedData
open FadicGate KoalaGateCheck
open KoalaWeightedRate (Envelope)
open KoalaFarBridge (rowCheck plainCheck)

def envelope : Envelope :=
  ⟨136,56,8,136,56,3536,4436,⟨9109900468,42691132881,55254610508⟩,3932638977573⟩
abbrev split:ℕ:=48
abbrev unit:ℕ:=1919967623040
abbrev terminal:ℕ:=72
abbrev gate:=KoalaSplitRow.rate envelope split unit

private def boxesTape : List (List Entry) := [
  b05l,b04u,b03z,b033,b035,b023,b00w,b00y,
  bzv,bzx,byt,byj.take 8++unpack 1 0x1c59aeb8,bwq.take 9++unpack 1 0x1baca3cb,bvs.take 6++unpack 4 0x49cad404c12e4c4a8e58e2982f598,bv2.take 10,bvh.take 10++unpack 1 0x1f62c3bc,
  btj.take 9++unpack 2 0x65247341e5,btw.take 10++unpack 2 0x4c96650247341e5,bu3.take 11++unpack 1 0x2169b93a,bsr.take 12++unpack 1 0x1d5c98c7,brn.take 10++unpack 3 0x4e18256490a9802a2fe3ae,bqp.take 11++unpack 4 0x494954a4e1aeca4c52e222a2fe3ae,bpj.take 13++unpack 3 0x494954a4b0fdb620665b52,bn5.take 8++unpack 9 0x24a4aa56f4cd4e3c4dda29c4a0a5504a4e9d84c535e84a4d99e3a62dea4,
  boc.take 11++unpack 6 0x6f49495424edc2ac4c93e3a498ad6630991c92,bml.take 11++unpack 7 0x6f49495424b0f9c84edbea84b0f5dc490ad6a31f3158c,bkr.take 14++unpack 4 0x49495424909d4c4d55a4e27d2c6c4,bl6.take 14++unpack 5 0x24a4aa12484ea63f4e9bec42b3332f6,bj9.take 14++unpack 5 0x2484ea63f4b505b04e1a6e42ee98cd7,bjp.take 13++unpack 7 0x24e5ebd3f494a1284d1525a4e9aeae4a4d1a636ac2e12,bgg.take 15++unpack 5 0x1fa4a50946f4f1b2c82ee91916,bgy.take 15++unpack 6 0x2567cfb24a50946f4b101ca4edaab8329f9e48,
  bh9.take 13++unpack 8 0x125284a37a4848b2268af10278dd6725072e3233bbc8f62,bbc.take 10++unpack 12 0x12f4c9137a4848b224a4ea5278e15326ecf62234a0b5284cd66684a8e1ac4a4d1904b42b93c,b5o.take 10++unpack 12 0x11f3181922206a125275292d416a13b6cb3931579134a4a4eb0270d55a234b109c44e4c7bd3,b7c.take 16++unpack 7 0x294491a064806dee49ca5404c956444f5d26c3ab91456,b4t.take 11++unpack 12 0x294653e0648499fa48c998e4f1ce624f5de1049095f449491d84c125e84b5320e49491924df5fda7,b4v.take 12++unpack 11 0x1491438f6064acedf8509d6145393e06428e9e44887dfc4d58dc449cd2224ea3083e,b4x.take 11++unpack 12 0x5245144f819384f8194b4f8188a229f032444ae527ceb012444cf17f550c329d,b24.take 11++unpack 12 0x14914b13e064e53e0622454a249f0229e8ef220e8af35f59c5e9b6,
  b2b.take 13++unpack 10 0x29224549122a48915e780f43,b2j.take 11++unpack 12 0xa489152448a922454916af42e2f,b0y.take 10++unpack 13 0xa489152448a922454914bd19dc7003fec2,b0z.take 9++unpack 14 0x29224549122a489152448a977704d1b,b10.take 8++unpack 15 0x149122a489152448a922454917d83419b,b11.take 7++unpack 16 0xa489152448a9224549122a48918396361b,b12.take 6++unpack 17 0x52448a9224549122a489152448a989ff6087,b0o.take 5++unpack 18 0x52448a9224549122a489152448a94a93e068d60a5a7,
  b66,b63,b68,b6b,[],[]]
def boxes (r : ℕ) : List FadicGate.Entry :=
  if r < 18 then [] else boxesTape.getD (r-18) []

def plain : ℕ → ℕ × ℕ × ℕ
  | 70 => (3914, 1630, 408)
  | 71 => (3980, 1650, 420)
  | _ => (0,0,0)

private def powersTape : List String := [
  "","","","","","","","",
  "","","","","","","","",
  "","","!#","!#&","!#&+","!#&)","!#%*0",z4F,
  "!#%)-8",z41,"!#%).29","!#%(.3;J","!#%(,4<CJ",z49,z6L,"!#%'-05>OM",
  z68,"!#$'+16@CQO",z3y,z3x,"!#$&*.48BOUUw","!#$&*.29CIWUo",z3o,"!#$&*/3:FDZY^~#!~#*~#&",
  "!#$&),4;AFTZYv~#.~#*~#&",z61,z5e,z3t,"!#$&(-15=JIZa_v~#9~#5~#1~#.",z5N,z3k,"!#$&),27?>LKgec~!~~#@~#=~#9~#5",
  "!!#%(,/7;?MLageu~#9~#@~#=~#9~#/","!!#%(,/47@NMYigm~#0~#D~#@~#=~#9","!!#%(*/28@INSkig~#(~#H~#D~#@~#=~#/","!!#%(+/38ADPNlki}~#@~#H~#D~#@~#:","!!#%'+/39BAQPflku~#8~#L~#H~#D~#<~#.","!!#%'+049CBRQ`nll~#0~#P~#L~#F~#<~#.",(zz75 ++ "#P~#I~#<~#."),(zz103 ++ "lw~#>~#S~#I~#<~#."),
  "!!#%'*-17:DITSlrlg~#0~#W~#I~#<~#.","!!#%'*.15;EDUSdrlg{~#E~#I~#<~#.","!!#%'*.15;EEVSZrlgi~#4~#I~#<~#.","!!#%'*.15<FEVSPrlgb~#!~#I~#<~#.","!!#$&),16<AEOSPhlgbm~#8~#<~#.","!!#$&),26<<EISP_lgb[~#&~#<~#.","!!#$&),26<;ECSPTlgb[q~#<~#.","!!#$'),/68;ECSPMlgb[_~#*~#.",
  "!!#$&),/35;ECSPMcgb[Vu~#.","!!#$&(,/15;ECLPMXgb[Vc~#.","!!#$&(+/15;@CFPMOgb[VPy","!!#$&(+/15;:CAPMJgb[VPg","!!#$&(+/15;:CAPMJ^b[VPT","",""]

def powers (r : ℕ) : List ℕ :=
  if r=0 then [] else KoalaSplitGateWords.powers (powersTape.getD (r-1) "")

private def plainPowers : ℕ → List ℕ
  | 70 => [0, 0, 1, 2, 3, 6, 8, 12, 15, 18, 24, 23, 32, 30, 45, 42, 39, 47, 60, 55, 49, 44, 38, 66, 70, 56, 42, 28, 14]
  | 71 => [0, 0, 1, 2, 4, 5, 8, 10, 15, 19, 21, 24, 33, 31, 39, 43, 40, 39, 62, 57, 51, 46, 41, 53, 75, 61, 48, 34, 20, 6]
  | _ => []

def tailPowers : List ℕ := KoalaSplitGateWords.powers "!!#$&'+,154:CACMJGb[VPKFoaRE7)"

def priced (r:ℕ):Bool:=rowCheck gate r (boxes r) (powers r) (plain r) (plainPowers r)
private theorem priced_list : (List.range 71).all (fun i => priced (i+1)) = true := by decide +kernel

theorem prices {r : ℕ} (hr : 0 < r) (hR : r < terminal) : priced r = true :=
  price hr hR priced_list

theorem tail:plainCheck gate terminal (4012,1650,550) tailPowers=true:=by decide +kernel

private abbrev Chunk (i n v : ℕ) := lossChunk 12 envelope plain boxes i n = v
private theorem checkPart (i n v : ℕ) (ok : Chunk i n v := by decide +kernel) : Chunk i n v := ok
private def part0 := checkPart 0 6 0x2384dc4cc14
private def part1 := checkPart 6 6 0x2384dc4cc14
private def part2 := checkPart 12 6 0x23823653989
private def part3 := checkPart 18 6 0x2327779765b
private def part4 := checkPart 24 6 0x2250284f238
private def part5 := checkPart 30 6 0x20bb4ab6c37
private def part6 := checkPart 36 6 0x1df91776da6
private def part7 := checkPart 42 6 0x19a0091c264
private def part8 := checkPart 48 6 0x133f6798228
private def part9 := checkPart 54 6 0xb91db24f17
private def part10 := checkPart 60 6 0x575fe420ca
private def part11 := checkPart 66 5 0x1d0f2b59f1

theorem loss_bound (N : ℕ) : Bound envelope terminal plain boxes 20783394792063 N :=
  loss_of_chunks 12 envelope terminal plain boxes 20783394792063 N (by decide) (by decide)
    (LossSum.empty _ _ _ _
      |>.append 6 0x2384dc4cc14 part0 |>.append 6 0x2384dc4cc14 part1 |>.append 6 0x23823653989 part2 |>.append 6 0x2327779765b part3
      |>.append 6 0x2250284f238 part4 |>.append 6 0x20bb4ab6c37 part5 |>.append 6 0x1df91776da6 part6 |>.append 6 0x19a0091c264 part7
      |>.append 6 0x133f6798228 part8 |>.append 6 0xb91db24f17 part9 |>.append 6 0x575fe420ca part10 |>.append 5 0x1d0f2b59f1 part11)

def receipt : KoalaSplitProof.Receipt envelope split unit :=
  ⟨terminal, plain, boxes, powers, plainPowers, tailPowers, 20783394792063,
    by decide,by decide,loss_bound,fun _ h h' => prices h h', tail⟩

end KoalaAt2428Gate20

#print axioms KoalaAt2428Gate20.loss_bound
#print axioms KoalaAt2428Gate20.receipt
