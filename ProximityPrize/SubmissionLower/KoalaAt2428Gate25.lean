import ProximityPrize.SubmissionLower.KoalaAt2428Gate23
import ProximityPrize.SubmissionLower.KoalaGateSharedData
import ProximityPrize.SubmissionLower.KoalaGateChunkSums
import ProximityPrize.SubmissionLower.KoalaSplitGateWords

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000

set_option linter.defProp false

namespace KoalaAt2428Gate25
open KoalaGateSharedData
open FadicGate KoalaGateCheck
open KoalaWeightedRate (Envelope)
open KoalaFarBridge (rowCheck plainCheck)

def envelope : Envelope :=
  ⟨132,56,8,135,56,3432,4435,⟨9783459364,48229992746,34714355811⟩,4205158099544⟩
abbrev split:ℕ:=48
abbrev unit:ℕ:=1919967640320
abbrev terminal:ℕ:=72
abbrev gate:=KoalaSplitRow.rate envelope split unit

private def boxesTape : List (List Entry) := [
  b05t,unpack 2 0x3159983ca,b04z,unpack 3 0x4a4d56c498b17e19fcbd32,unpack 4 0x12b3b6913831c59834a,b03o,b02m,b01e,
  b01h.take 3++unpack 3 0x4ace9b04a8e9ac1db32578,b00d,bz2,bz9.take 5++unpack 3 0x4a0ddd44b0edb41d06290f,bxt,bxz.take 4++unpack 5 0x49cbd5c4b9261c4acf1ce4a8e59225ccc725,by4.take 4++unpack 5 0x48ca17a4c535fc4b0fdcc4a8dda028297ec9,bwa.take 8++unpack 2 0x4b52a041b00297a,
  bwj.take 5++unpack 5 0x4a0cd7c4c5321c49cb9824b101c6292c9451,bur.take 6++unpack 5 0x4d98ea049cb5484c536564a8e58c287fc330,bux.take 4++unpack 7 0x4c55214494a58e4c93e224b109ba4a8e1a04a4d5a4319ca5b9,bte,bsf.take 6++unpack 7 0x4b4fdd04e5badc494a9444c12e144a4cd904b501c62f962400,brd.take 6++unpack 8 0x49499484d15e524c96a564a0a9464c5525e4a0ad544b10dd831f2ea18,bqa.take 6++unpack 9 0x494994849499484e5bae44c11dc24949d604d162524a4e5b04a8d1aa344f766e,bp2,
  unpack 16 0x494994848c9d404cd4e684e18a5e490a57c4c132004aceda24b509de4ace9b04a8d5ac7a939a35c343834a3f5b72,bnn,bns.take 8++unpack 9 0x48c9d4049491444b0fdb64f1bed449ce1c04a0a1504cd6a6649cb55a35a943f2,bm2,bm6.take 9++unpack 9 0x4a0bd7e4909154490953e4f5d2be4c9464a498ad624bd2a1a4acf1ba37af9a56,bkg,bkn.take 9++unpack 10 0x4a8fdd0490953e49499464d15e524edc2c6494b5724a0a9464d17e76498b17c3bbc8f51,biy,
  bj5.take 8++unpack 12 0x4b936184949946494a1504b0fda84e5bb004c925d8494a56c4b91e0a4b519d04a8dda04b0f9c2452f9947,bg5,bgb.take 10++unpack 11 0x4cd7268494a1504949d2849091524f1bed64dd969c494a940490a57e4e18e8a49cb57e4225f3b4,bcm,bct.take 9++unpack 13 0x4e1b6c24949d28490915248c915e4d1662a4f1bed84a4edd0494995c4c536024bd29f8498a9524c1360e4b993776,b6j,b6q.take 11++unpack 12 0x50dda60478adde48c8982494913c4b10db64f5bad44c15e4a4a4b1544949d5c4e1aeba498a96e48392212,b1d,
  b1i.take 10++unpack 14 0x266a50a1f44cf1a647c79c248c95624f5d68e4f9f23849095ce49091d44c52df24b12a0649ca1a24c9460652590b90,b1o.take 11++unpack 13 0x49f4b911d0424ada44ace5ea50dee385456634420d1a248879f64d991ce4a0de2e49095a64e4c98ac,b1u.take 12++unpack 12 0x127c4a1666be274ad142a4c9340942cf18a48485b4501ea1c48899e050a90774,b1z.take 6++unpack 18 0x93e25243864941669d84894b909c44411dc2549462c418f5a64b515d44a4b6084b501ee494c1fe4acddcc490bdec65ec8155,b26.take 8++unpack 16 0x49f1224f89127c489428fd984c94a18480a5784b4fdee4a8d21064e89248,b2e.take 6++unpack 18 0x49f1224f89127c4894bd0dca4cd4a1641119524b9061049ccdda498c20049cb9fa6bffa0ce,b2n.take 7++unpack 17 0x127c4893e2449f1224f894a8e59c4395dda4a5099a49cbe086daf2ffe,b0z.take 6++unpack 18 0x93e2449f1224f89127c4894bd19d843139c8498fd7049cbde673c232e0,
  b10.take 6++unpack 18 0x49f1224f89127c4893e2449f4c129ec41529904a5019c76cbf533,b11.take 6++unpack 18 0x24f89127c4893e2449f1224f894b915d442d4dac7b2dc501,b12.take 6++unpack 18 0x127c4893e2449f1224f89127c4894c525ea89529df0,b0o.take 5++unpack 19 0x93e2449f1224f89127c4893e2449f4a125e88cb3e30e,b3y,bq.take 24,bs.take 24,bt.take 24,
  [],[]]
def boxes (r : ℕ) : List FadicGate.Entry :=
  if r < 14 then [] else boxesTape.getD (r-14) []

def plain : ℕ → ℕ × ℕ × ℕ
  | 70 => (3914, 1630, 408)
  | 71 => (3980, 1650, 420)
  | _ => (0,0,0)

private def powersTape : List String := [
  "","","","","","","","",
  "","","","","","","!$","!$",
  "!#'","!#'-","!#&*","!#&+4","!#&+/8","!#&)/5","!#%*06B","!#&*17DB",
  z5k,"!#%)-38FO",z59,z3q,z6N,z49,z67,z40,
  "!#$(+06?IOVw",z5W,z56,z3w,"!#$&*.48BOUVw~#!{u",z4B,z64,z5p,
  "!#$&),4;AFTZYv~#.~#*~#&u","!#$&)-4;<GN]Zn~#1~#.~#*~##","!#$&)-17;HH_]f~#)~#1~#.~#*u",z52,(zz93 ++ "~#.u"),z2u,"!#$&(,16>@KNecf~#(~#=~#9~#5~#/u",z2g,
  "!!#%(,/7;?MLageu~#9~#A~#=~#9~#/u","!!#%(,/47@NMYhgm~#0~#E~#A~#=~#9~##","!!#%(*/38@INSkhg~#(~#H~#E~#A~#=~#/u","!!#%(+/38ADONlkh}~#@~#H~#E~#A~#:~##","!!#%'+/39BAPOflku~#8~#L~#H~#D~#A~#/t","!!#%'+049CBRP`nlm~#0~#P~#L~#H~#A~#3~##","!!#%'+-4:>CSRYpnl~#(~#H~#P~#L~#A~#3~#$",(zz103 ++ "n{~#@~#T~#O~#A~#3~#$"),
  "!!#%'*.17:DITSlrnh~#5~#X~#O~#A~#3~#$","!!#%'*.15;EDUTfsnh~#!~#K~#O~#A~#3~#$","!!#%'*.15;FEVT[snhm~#9~#O~#A~#3~#$","!!#%'*.15<FEWTQsnhc~#&~#O~#A~#3~#$","!!#$&),16<BEPTQjnhcq~#=~#A~#3~#$","!!#$&),26==EITQ`nhc^~#*~#A~#3~#$","!!#$'),26=;ECTQVnhc]u~#A~#3~#$","!!#$')-/68;ECTQNnhc]b~#.~#3~#$",
  "!!#$&)-/35;ECTQNdhc]Wy~#3~#$","!!#$&(-/15;ECMQNZhc]Wg~#3~#$","!!#$&(+/15;@CFQNPhc]WS}~#$","!!#$&(+/15;;CAQNKhc]WQk~#$","!!#$&(+/15;:CAQNK_c]WQW~#$","",""]

def powers (r : ℕ) : List ℕ :=
  if r=0 then [] else KoalaSplitGateWords.powers (powersTape.getD (r-1) "")

private def plainPowers : ℕ → List ℕ
  | 70 => [0, 0, 1, 2, 4, 6, 8, 12, 15, 19, 25, 23, 32, 31, 46, 43, 40, 48, 62, 57, 51, 46, 40, 71, 75, 61, 47, 33, 18, 4]
  | 71 => [0, 0, 1, 2, 4, 5, 8, 10, 15, 19, 21, 24, 33, 31, 40, 44, 41, 41, 64, 59, 53, 48, 42, 58, 81, 67, 53, 38, 24, 10]
  | _ => []

def tailPowers : List ℕ := KoalaSplitGateWords.powers "!!#$&'+,155:CADNKHd^XRMKugWI;-"

def priced (r:ℕ):Bool:=rowCheck gate r (boxes r) (powers r) (plain r) (plainPowers r)
private theorem priced_list : (List.range 71).all (fun i => priced (i+1)) = true := by decide +kernel

theorem prices {r : ℕ} (hr : 0 < r) (hR : r < terminal) : priced r = true :=
  price hr hR priced_list

theorem tail:plainCheck gate terminal (4012,1650,550) tailPowers=true:=by decide +kernel

private theorem exactLoss0 : lossChunk 1 envelope plain boxes 0 24 = 9727066615133 :=
  by decide +kernel

private theorem exactLoss24 : lossChunk 1 envelope plain boxes 24 24 = 8430294092818 :=
  by decide +kernel

private theorem exactLoss48 : lossChunk 1 envelope plain boxes 48 23 = 2562435054247 :=
  by decide +kernel

theorem loss_bound (N : ℕ) : Bound envelope terminal plain boxes 20719795762198 N :=
  loss_of_chunks 1 envelope terminal plain boxes 20719795762198 N (by decide) (by decide)
    (LossSum.empty _ _ _ _
      |>.append 24 9727066615133 exactLoss0
      |>.append 24 8430294092818 exactLoss24
      |>.append 23 2562435054247 exactLoss48)

def receipt : KoalaSplitProof.Receipt envelope split unit :=
  ⟨terminal, plain, boxes, powers, plainPowers, tailPowers, 20719795762198,
    by decide,by decide,loss_bound,fun _ h h' => prices h h', tail⟩

end KoalaAt2428Gate25

#print axioms KoalaAt2428Gate25.loss_bound
#print axioms KoalaAt2428Gate25.receipt
