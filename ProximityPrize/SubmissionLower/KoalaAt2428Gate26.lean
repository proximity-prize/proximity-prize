import ProximityPrize.SubmissionLower.KoalaAt2428Gate25
import ProximityPrize.SubmissionLower.KoalaGateSharedData
import ProximityPrize.SubmissionLower.KoalaGateChunkSums
import ProximityPrize.SubmissionLower.KoalaSplitGateWords

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000

set_option linter.defProp false

namespace KoalaAt2428Gate26
open KoalaGateSharedData
open FadicGate KoalaGateCheck
open KoalaWeightedRate (Envelope)
open KoalaFarBridge (rowCheck plainCheck)

def envelope : Envelope :=
  ⟨136,55,12,137,55,3536,4437,⟨9703446922,54326661093,11485746960⟩,4281645159196⟩
abbrev split:ℕ:=48
abbrev unit:ℕ:=1919968368000
abbrev terminal:ℕ:=71
abbrev gate:=KoalaSplitRow.rate envelope split unit

private def boxesTape : List (List Entry) := [
  b05u,b050,b04t,b040,b03d,unpack 5 0x951cb0494383236faa46,b02b,b00e.take 4++unpack 2 0x4ace9b21cafd621,
  bz3.take 6,bzb.take 5++unpack 2 0x4ace9ac1d0645fb,bzg,by1.take 8,by8,bwc.take 8++unpack 1 0x1b00297a,bvt.take 5++unpack 5 0x4a0d9864c12a144a0c18e4b101c629830418,but.take 10,
  buf,btf.take 7++unpack 4 0x4a4f5d24b0e9a24b511da29831282,bsh.take 8++unpack 4 0x4e5c2e6498a9444c12e16287fee99,bts,bqc.take 9++unpack 3 0x4c525ce4949d62277c73dc,bqh.take 10++unpack 3 0x4f5cec449cbd8c277c73dc,bp8.take 11++unpack 3 0x4cd5e7c4e5926a277c73dc,bpe.take 7++unpack 8 0x494994e4e9c2e44c53a30494a9424d97a644989d604b929dc38b314f4,
  bnv.take 9++unpack 7 0x494994e4b0fdb64f5ceea49cd9b64a4ad5c4cd6a6833f9407d,bo3,bm9.take 11++unpack 6 0x4909154490953e4f5daca4d15256494a1562f3f7a64,bmi,bkq.take 10++unpack 8 0x490953e49499464d5665e4f1ced2490b5744a0a9464d17e7a3a0c9a41,bl2,bj8.take 11++unpack 8 0x494994649499484b105b04e9c70c4c92de649499604bd2e1a3a0c5202,bjm,
  bfm.take 7++unpack 14 0x266b93424a4ca424a529824848a9278e571270c94f24c5aa72464cb8274d556234c5360e498ad524acfdac4e4c506a,bgu,bcw,bdc,b6t.take 14++unpack 8 0x4808a1848871b049499464b10db64f5c2e24c96e5a4a0a5463cbf6ae1,b4s.take 8++unpack 15 0x4e17e5443881b647c61d049895564cd66584fdf2764acf61a4949d8c4a4edbc4d96a70498b5804c94a08498a9524b0fdda5712a64a,b1k.take 12++unpack 11 0x16a2462cd24230f824442ca27cf53827d011b248450024842e90f4b12e084a965bc0,b1q,
  b1w,b22,b29,b2h,b0y.take 9++unpack 15 0x26b49935a4c9ad264d6934c125f242d39dc694bae09,b2v,b33,b39,
  b3k,b3o,b40,b3u,b49,b4b,[]]
def boxes (r : ℕ) : List FadicGate.Entry :=
  if r < 16 then [] else boxesTape.getD (r-16) []

def plain : ℕ → ℕ × ℕ × ℕ
  | 70 => (3914, 1630, 408)
  | _ => (0,0,0)

private def powersTape : List String := [
  "","","","","","","","",
  "","","","","","","","",
  "!#","!#","!#&","!#&+","!#&+/",z3r,z2Q,z4F,
  "!#%)-8>","!#%)-38F",z5l,z3q,"!#%(,4<CJ","!#%(,4==LO","!#$',08=ML",z40,
  z69,z4M,z3y,z3x,"!#$&*.48BOUVw","!#$&*/29CIWUo~#&",z3o,"!#$&*/3:ED[Y^~!~~#*~#&",
  z60,"!#$&)-4<<GN][n~#1~#.~#*",z5f,z3t,z5Q,z5N,z4t,z2g,
  z2s,z4X,z4W,"!!#%(+/38AEONlji}~#@~#H~#D~#A~#:","!!#%'+/39BAQOflju~#8~#L~#H~#E~#A~#/","!!#%'+049CBRP`nlm~#0~#P~#L~#H~#B~#4",(zz75 ++ "#P~#L~#B~#4~#&"),(zz103 ++ "mz~#@~#T~#P~#B~#4~#&"),
  "!!#%'*-17:DITSlrmh~#4~#X~#P~#B~#4~#&","!!#%'*.15;EDUSesmh~!~~#K~#P~#B~#4~#&","!!#%'*.15;FEVSZsmhl~#9~#P~#B~#4~#&","!!#%'*.15<FEVSPsmhc~#&~#P~#B~#4~#&","!!#$&),16<AEOSPimhcp~#=~#B~#4~#&","!!#$&),26<<EISP_mhc^~#+~#B~#4~#&","!!#$&),26<;ECSPUmhc]u~#B~#4~#&","!!#$'),/68;ECSPMmhc]b~#/~#4~#&",
  "!!#$&),.25;ECSPMdhc]Wz~#4~#&","!!#$&(,.15;ECLPMYhc]Wg~#4~#&","!!#$&(*.15;?CFPMOhc]WS~!~~#&","!!#$&(*.15;:CAPMJhc]WRl~#&","!!#$&(*.15;:CAPMJ^c]WRX~#&",""]

def powers (r : ℕ) : List ℕ :=
  if r=0 then [] else KoalaSplitGateWords.powers (powersTape.getD (r-1) "")

private def plainPowers : ℕ → List ℕ
  | 70 => [0, 0, 1, 2, 4, 6, 8, 12, 15, 19, 24, 23, 32, 30, 45, 42, 39, 47, 61, 56, 51, 45, 40, 71, 76, 62, 48, 34, 20]
  | _ => []

def tailPowers : List ℕ := KoalaSplitGateWords.powers "!!#$&'*,157:CAJMJJc]WRL^vgXJ<."

def priced (r:ℕ):Bool:=rowCheck gate r (boxes r) (powers r) (plain r) (plainPowers r)
private theorem priced_list : (List.range 70).all (fun i => priced (i+1)) = true := by decide +kernel

theorem prices {r : ℕ} (hr : 0 < r) (hR : r < terminal) : priced r = true :=
  price hr hR priced_list

theorem tail:plainCheck gate terminal (4012,1650,550) tailPowers=true:=by decide +kernel

private theorem exactLoss0 : lossChunk 1 envelope plain boxes 0 24 = 9732304855968 :=
  by decide +kernel

private theorem exactLoss24 : lossChunk 1 envelope plain boxes 24 24 = 8428582532688 :=
  by decide +kernel

private theorem exactLoss48 : lossChunk 1 envelope plain boxes 48 22 = 2500830135138 :=
  by decide +kernel

theorem loss_bound (N : ℕ) : Bound envelope terminal plain boxes 20661717523794 N :=
  loss_of_chunks 1 envelope terminal plain boxes 20661717523794 N (by decide) (by decide)
    (LossSum.empty _ _ _ _
      |>.append 24 9732304855968 exactLoss0
      |>.append 24 8428582532688 exactLoss24
      |>.append 22 2500830135138 exactLoss48)

def receipt : KoalaSplitProof.Receipt envelope split unit :=
  ⟨terminal, plain, boxes, powers, plainPowers, tailPowers, 20661717523794,
    by decide,by decide,loss_bound,fun _ h h' => prices h h', tail⟩

end KoalaAt2428Gate26

#print axioms KoalaAt2428Gate26.loss_bound
#print axioms KoalaAt2428Gate26.receipt
