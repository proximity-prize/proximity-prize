import ProximityPrize.SubmissionLower.KoalaAt2428Gate16
import ProximityPrize.SubmissionLower.KoalaGateSharedData
import ProximityPrize.SubmissionLower.KoalaGateChunkSums
import ProximityPrize.SubmissionLower.KoalaSplitGateWords

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000

set_option linter.defProp false

namespace KoalaAt2428Gate17
open KoalaGateSharedData
open FadicGate KoalaGateCheck
open KoalaWeightedRate (Envelope)
open KoalaFarBridge (rowCheck plainCheck)

def envelope : Envelope :=
  ⟨132,56,12,133,56,3432,4433,⟨10235763371,53429788596,12703733035⟩,4336787284417⟩
abbrev split:ℕ:=48
abbrev unit:ℕ:=1919968360320
abbrev terminal:ℕ:=71
abbrev gate:=KoalaSplitRow.rate envelope split unit

private def boxesTape : List (List Entry) := [
  b05q,b04z,unpack 3 0x4a8d972498b17e19fcbd32,b048,b03c,b02l,unpack 5 0x12a386012a505ecc03236faa46,b01h.take 3++unpack 3 0x4acf1b84ace5ac1db3088c,
  b00d.take 3++unpack 3 0x4acf1ba4a8e5aa1fb97bcb,bz2.take 4++unpack 3 0x4b922184a8edb61e099547,bz8,bxt.take 5++unpack 3 0x4bd2a204a4dda01fb97bdf,bxz,by4.take 4++unpack 5 0x48c9d704c93e0c4acfdcc4acdd9e282961db,bw9,bwj,
  bur,bux,bte.take 5++unpack 6 0x4a8f9d84ace9a04b511d84b4fdf04a8eda430997359,bsf,brd,bqa,bp2.take 6++unpack 9 0x49499464b0f5c44f1d2ce4a0bd8a4a4edb84bd22144b909de4a4d98a3702c936,bp5.take 6++unpack 10 0x494994648c95364cd5a744e99672488996e4c53e0a4aceda24b905de4acf5be39b60d8c,
  bnn.take 7++unpack 9 0x48c953649491444e9caee4c12e22498b54e4d9765e4949d604bd25da38063567,bns,bm2.take 7++unpack 10 0x494914449091504d162564e1bab84a09d4c4a4e5d04c541fc4a8e1a84acedb03c6934f9,bm6,bkg.take 9++unpack 9 0x490915049099464b4fdce4f5d6c84b0f9e248ca9644d9726c49cbd5c395fbab3,bkn,biy.take 8++unpack 11 0x4909946494994649099464e9cad44d97a7c4a4b1524a0e1ae4cd4e44494ad544c1221242d2b64b,bj5,
  bg5.take 11++unpack 9 0x4a0c17c4909946498a1304d15e644edc6cc4a4cda0498b14e4cd66843cbf965e,bgb,bcm.take 8++unpack 13 0x4a8ede2498a13048c91504b0f9be4f5cee84c94a2848c996e4acf1aa4d15e6c498b14e4c52e0e4a0d98c4c45fa1b,bct,b6j.take 10++unpack 12 0x4c1321c48c9150490895249099464f5dac84e5aedc494a96c4a0b1264d1767c4ace9b84a4d18e493c546e,b6q,b1d.take 7++unpack 16 0x4e176484249d5c4887d9249ca12e4cd62544f5de964b10dfe498998a4a0e9ba4d96a6c494a96c4cd5218498a9504b509ee4a0d9ba5919368c,b1i,
  b1o,b1u,b21,b28,unpack 24 0xdeab76f55bb7aaddba6296f6268a70a2027a7f25c83082526ef824858f524e5cfd2505cff493a54583797f4983,b2p,b2u,b32,
  b11.take 7++unpack 17 0x6f55bb7aaddbd56edeab76f55bb783963630,b12.take 6++unpack 18 0x37aaddbd56edeab76f55bb7aaddbd589ff6099,b0o.take 5++unpack 19 0x37aaddbd56edeab76f55bb7aaddbd54a93e008d60a5b6,b0q.take 5++unpack 19 0x1bd56edeab76f55bb7aaddbd56edeab790125516,bq.take 4++unpack 20 0xdeab76f55bb7aaddbd56edeab76f55bb796254993,bs.take 3++unpack 21 0x6f55bb7aaddbd56edeab76f55bb7aaddbd59c8e73fc,unpack 24 0x37aaddbd56edeab76f55bb7aaddbd56edeaa1e9f0023486605d95824cd4,[]]
def boxes (r : ℕ) : List FadicGate.Entry :=
  if r < 15 then [] else boxesTape.getD (r-15) []

def plain : ℕ → ℕ × ℕ × ℕ
  | 70 => (3914, 1630, 408)
  | _ => (0,0,0)

private def powersTape : List String := [
  "","","","","","","","",
  "","","","","","","","!$",
  "!#'","!#'","!#&*","!#&+4","!#&+/","!#&)/5",z2Q,"!#&*17D",
  z5k,"!#%)-38F",z59,z3q,z6N,z49,z67,z40,
  z69,z5W,z56,z3w,z6j,z4B,z6E,"!#$&*/3:EDZY^~!~~#*~#&~#!",
  z5z,z3K,z3u,z31,z5P,"!#$%(+16>EJTcam~#1~#9~#5~#1~##",("!#$&(," ++ zz96),z2g,
  z2s,"!!#%(,/47@NMZigm~#0~#D~#A~#=~#9~##",z4W,"!!#%(+/38AEONlji}~#@~#H~#D~#A~#:~##","!!#%'+/39BAPOfljt~#8~#L~#H~#D~#A~#/","!!#%'+049CBRP`nll~#0~#P~#L~#H~#C~#4~##",(zz75 ++ "#P~#L~#C~#4~#&"),(zz103 ++ "n{~#@~#T~#P~#C~#4~#&"),
  "!!#%'*.17:DITSlrni~#6~#X~#Q~#C~#4~#&","!!#%'*.15;EDUSesnh~##~#M~#Q~#C~#4~#&","!!#%'*.15;EEVS[snhm~#:~#Q~#C~#4~#&","!!#%'*.15<FEVSQsnhc~#'~#Q~#C~#4~#&","!!#$&),16<AEPSPjnhcq~#>~#C~#4~#&","!!#$&),26<<EISP`nhc_~#,~#C~#4~#&","!!#$'),26<;ECSPUnhc^v~#C~#4~#&","!!#$'),/68;ECSPNnhc^c~#0~#4~#&",
  "!!#$&),.35;ECSPNdhc^Wz~#4~#&","!!#$&(,.15;ECMPNYhc^Wh~#4~#&","!!#$&(+.15;@CFPNPhc^WT~#!~#&","!!#$&(+.15;;CAPNKhc^WRl~#&","!!#$&(+.15;:CAPNK_c^WRX~#&",""]

def powers (r : ℕ) : List ℕ :=
  if r=0 then [] else KoalaSplitGateWords.powers (powersTape.getD (r-1) "")

private def plainPowers : ℕ → List ℕ
  | 70 => [0, 0, 1, 2, 4, 6, 8, 12, 15, 19, 24, 23, 32, 30, 45, 42, 39, 47, 61, 56, 51, 45, 40, 71, 76, 62, 47, 33, 19, 4]
  | _ => []

def tailPowers : List ℕ := KoalaSplitGateWords.powers "!!#$&'+,157:CAJNKKc^WRM^vgXJ;-"

def priced (r:ℕ):Bool:=rowCheck gate r (boxes r) (powers r) (plain r) (plainPowers r)
private theorem priced_list : (List.range 70).all (fun i => priced (i+1)) = true := by decide +kernel

theorem prices {r : ℕ} (hr : 0 < r) (hR : r < terminal) : priced r = true :=
  price hr hR priced_list

theorem tail:plainCheck gate terminal (4012,1650,550) tailPowers=true:=by decide +kernel

private theorem exactLoss0 : lossChunk 1 envelope plain boxes 0 24 = 9729220059931 :=
  by decide +kernel

private theorem exactLoss24 : lossChunk 1 envelope plain boxes 24 24 = 8437963142099 :=
  by decide +kernel

private theorem exactLoss48 : lossChunk 1 envelope plain boxes 48 22 = 2538411991025 :=
  by decide +kernel

theorem loss_bound (N : ℕ) : Bound envelope terminal plain boxes 20705595193055 N :=
  loss_of_chunks 1 envelope terminal plain boxes 20705595193055 N (by decide) (by decide)
    (LossSum.empty _ _ _ _
      |>.append 24 9729220059931 exactLoss0
      |>.append 24 8437963142099 exactLoss24
      |>.append 22 2538411991025 exactLoss48)

def receipt : KoalaSplitProof.Receipt envelope split unit :=
  ⟨terminal, plain, boxes, powers, plainPowers, tailPowers, 20705595193055,
    by decide,by decide,loss_bound,fun _ h h' => prices h h', tail⟩

end KoalaAt2428Gate17

#print axioms KoalaAt2428Gate17.loss_bound
#print axioms KoalaAt2428Gate17.receipt
