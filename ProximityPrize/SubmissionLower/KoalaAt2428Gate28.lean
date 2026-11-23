import ProximityPrize.SubmissionLower.KoalaAt2428Gate27
import ProximityPrize.SubmissionLower.KoalaGateSharedData
import ProximityPrize.SubmissionLower.KoalaGateChunkSums
import ProximityPrize.SubmissionLower.KoalaSplitGateWords

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000

set_option linter.defProp false

namespace KoalaAt2428Gate28
open KoalaGateSharedData
open FadicGate KoalaGateCheck
open KoalaWeightedRate (Envelope)
open KoalaFarBridge (rowCheck plainCheck)

def envelope : Envelope :=
  ⟨128,56,2,131,56,3328,4431,⟨10225060532,52290124620,13664037060⟩,4251616166374⟩
abbrev split:ℕ:=48
abbrev unit:ℕ:=1919967496320
abbrev terminal:ℕ:=71
abbrev gate:=KoalaSplitRow.rate envelope split unit

private def boxesTape : List (List Entry) := [
  b05q,b04z,unpack 3 0x4a0c95c498b17e19fcbd32,unpack 4 0x12a3a6713831c59834a,unpack 4 0x129356026831eb64962,b02n,b01f,b01k,
  b00e,bz3,bzb,bzh,by1,by8.take 7++unpack 2 0x490a17a1b567c52,bwc,bwn,
  but,buf,btf,bsh,brf,bqc,bqh,bp8,
  bpe,bnv,bo3.take 12++unpack 5 0x498994c48c91544d562544e1b2b22adcc32f,bm9,bmi.take 9++unpack 9 0x48c9154494953e4b0fdd24f5d6c44b0f9e6490ad664d96a6249cc96c3a62fb90,bkq,bl2.take 14++unpack 5 0x494953e490994849499464edcede29832103,bj8,
  bjm.take 13++unpack 7 0x49cbd764949946494a5324d15a604f1cad44a4cda235529a5b,bfm.take 8++unpack 13 0x266b93524a4ca324a529924848aa278e16b272cf5624a54a024852bf272cf4f234c5360e498ad524a95bccb,bgu.take 12++unpack 9 0x4a8f1e4494a53249091544b0fdc04f1c2d84c94a2a490a57e4acf1ac3c12ff17,bcw.take 14++unpack 8 0x4e1aeba494a532490915448c89524d56e384f5cee64a4e9d0385c96d4,bdc.take 10++unpack 12 0x4bd3a20490915448c89524949d484f5d2c44e5b6e24949d5e4a0bd364d172724ace9ba4a8dda24a95e826,b6t,b4s.take 9++unpack 14 0x4e57a4c424a540488819449ca12e4cd665c4f9da904ad0e02494917c4a8f9ce4d55e5e498b5804c94a08498a9525305dca8,b1k,
  b1q.take 14++unpack 10 0xbb34b911c8424ad644b0f1d450dee6454d7e74420d14448471e8437f4d4c,b1w.take 10++unpack 14 0x2eccba1666a0274ad272a4c93617439155848489b6501ee2048899e24a0bdfc4b912025918d0e4,b23,b2a,b2i,b0y,b0z,b10,
  b11,b12,b13,b15,b14,b16,unpack 24 0x17665cbb32e5d9972eccb97665cbb32e5d9a1e9eff234865e5d95824cd4,[]]
def boxes (r : ℕ) : List FadicGate.Entry :=
  if r < 15 then [] else boxesTape.getD (r-15) []

def plain : ℕ → ℕ × ℕ × ℕ
  | 70 => (3914, 1630, 408)
  | _ => (0,0,0)

private def powersTape : List String := [
  "","","","","","","","",
  "","","","","","","","!$",
  "!#'","!#'-","!#&*","!#&+4","!#&+/8","!#&)/5","!#%*06B","!#&*17DB",
  z5k,"!#%)-38F",z59,z3q,z6N,"!#%(,4==KN","!#$',08=MKg",z40,
  "!#$(+06?IOVw",z5W,z56,z3w,z6j,"!#$&*/29CIWUo~#&~#!{",z6E,"!#$&*/3:ED[Y^~#!~#*~#&~#!",
  z60,"!#$&)-4<<GN][n~#1~#.~#*~##",z5f,z52,z5Q,z2u,z4t,z4m,
  z2s,z4X,"!!#%(*/38@INSkig~#(~#H~#D~#A~#=~#/","!!#%(+/38AEONlki}~#@~#H~#D~#A~#:~##","!!#%'+/39BAQOflku~#8~#L~#H~#D~#A~#/","!!#%'+049CBRQ`nlm~#0~#P~#L~#H~#A~#3~##",(zz75 ++ "#P~#L~#A~#3~#%"),(zz103 ++ "my~#@~#T~#O~#A~#3~#%"),
  "!!#%'*-17:DITSlrmh~#3~#X~#O~#A~#3~#%","!!#%'*.15;EDUSdrmh~!~~#J~#O~#A~#3~#%","!!#%'*.15;EDVSZrmhk~#8~#O~#A~#3~#%","!!#%'*.15<FDVSPrmhb~#%~#O~#A~#3~#%","!!#$&),16<ADOSPimhbp~#<~#A~#3~#%","!!#$&),26<<DHSP_mhb]~#*~#A~#3~#%","!!#$&),26<;DCSPTmhb]t~#A~#3~#%","!!#$'),/68;DCSPMmhb]b~#.~#3~#%",
  "!!#$&),.25;DCSPMchb]Wy~#3~#%","!!#$&(,.15;DCLPMYhb]Wf~#3~#%","!!#$&(*.15;?CFPMOhb]WS}~#%","!!#$&(*.15;:CAPMJhb]WQk~#%","!!#$&(*.15;:CAPMJ^b]WQW~#%",""]

def powers (r : ℕ) : List ℕ :=
  if r=0 then [] else KoalaSplitGateWords.powers (powersTape.getD (r-1) "")

private def plainPowers : ℕ → List ℕ
  | 70 => [0, 0, 1, 2, 4, 6, 8, 12, 15, 19, 24, 23, 32, 30, 45, 42, 39, 48, 62, 56, 51, 46, 40, 73, 77, 63, 50, 36, 22, 8]
  | _ => []

def tailPowers : List ℕ := KoalaSplitGateWords.powers "!!#$&'*,157:CAJMKJc^XRM`wiZL>1"

def priced (r:ℕ):Bool:=rowCheck gate r (boxes r) (powers r) (plain r) (plainPowers r)
private theorem priced_list : (List.range 70).all (fun i => priced (i+1)) = true := by decide +kernel

theorem prices {r : ℕ} (hr : 0 < r) (hR : r < terminal) : priced r = true :=
  price hr hR priced_list

theorem tail:plainCheck gate terminal (4012,1650,550) tailPowers=true:=by decide +kernel

private theorem exactLoss0 : lossChunk 1 envelope plain boxes 0 24 = 9727671056567 :=
  by decide +kernel

private theorem exactLoss24 : lossChunk 1 envelope plain boxes 24 24 = 8426159894673 :=
  by decide +kernel

private theorem exactLoss48 : lossChunk 1 envelope plain boxes 48 22 = 2553053343332 :=
  by decide +kernel

theorem loss_bound (N : ℕ) : Bound envelope terminal plain boxes 20706884294572 N :=
  loss_of_chunks 1 envelope terminal plain boxes 20706884294572 N (by decide) (by decide)
    (LossSum.empty _ _ _ _
      |>.append 24 9727671056567 exactLoss0
      |>.append 24 8426159894673 exactLoss24
      |>.append 22 2553053343332 exactLoss48)

def receipt : KoalaSplitProof.Receipt envelope split unit :=
  ⟨terminal, plain, boxes, powers, plainPowers, tailPowers, 20706884294572,
    by decide,by decide,loss_bound,fun _ h h' => prices h h', tail⟩

end KoalaAt2428Gate28

#print axioms KoalaAt2428Gate28.loss_bound
#print axioms KoalaAt2428Gate28.receipt
