import ProximityPrize.SubmissionLower.KoalaAt2428Gate20
import ProximityPrize.SubmissionLower.KoalaGateSharedData
import ProximityPrize.SubmissionLower.KoalaGateChunkSums
import ProximityPrize.SubmissionLower.KoalaSplitGateWords

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000

set_option linter.defProp false

namespace KoalaAt2428Gate21
open KoalaGateSharedData
open FadicGate KoalaGateCheck
open KoalaWeightedRate (Envelope)
open KoalaFarBridge (rowCheck plainCheck)

def envelope : Envelope :=
  ⟨136,56,10,136,56,3536,4436,⟨9494350246,45893571558,43929303453⟩,4109460306808⟩
abbrev split:ℕ:=48
abbrev unit:ℕ:=1919968005120
abbrev terminal:ℕ:=72
abbrev gate:=KoalaSplitRow.rate envelope split unit

private def boxesTape : List (List Entry) := [
  b05k,b04t,b040,b03d,b033,b02b,b00d.take 3++unpack 3 0x4ace5aa4a8e9ac200feb90,unpack 6 0x12b3b6e12b396d929356881832a2fa9c6,
  bzb.take 6++unpack 1 0x19500918,bzh.take 7,unpack 8 0x9724c3c959eba0951bb10959c3449cd8730efa946,bxc.take 4++unpack 5 0x48ca57a4c531fe4acf9c44acdda0287fd1a2,unpack 9 0x969cb54951eb84961f3b8961f348951ab593418335a93576,unpack 10 0x949a3009825c289397308962038c961db88951c31d341873805d042,unpack 10 0x9396a8c98264a4951cb18959f3909519338951d3380c39b3a0c6ede,unpack 11 0x992a42c9213b1099284489621378959c3409419b30959cb481cd833c6934f6,
  unpack 11 0x949e3a4959db4496a13a0969f3cc951db4c959bb58949a3306c1873ec5cfc2,unpack 12 0x4e5b6d8498b54e4bd260c4a8cd924b105c84ace9b04a949a3300c383412295da,bts.take 10++unpack 2 0x4c96e5a23700f7f,bqc.take 5++unpack 7 0x4c119ba498a56e4cd5e484a4dda64a4d1aa4b911d839091f8e,unpack 14 0x961eb889d37d609417b1c949e37497a341896a03a4949bb18959bb78949cb3494983002c68747e2955a,bp8.take 5++unpack 10 0x2464c9d264a732272c53224652be26096fb25676d225a82ee25878da213d6c3c07,unpack 16 0x48c993a494994e4e5b2ce4c13228498a9424d572584989d604b929dc4acd1ca4a4e5884ace5a69a1c18b4b99715b,unpack 17 0x48c993a494994e4b0f9b04edbad24a0d9b64a0a5504cd6a68498b55c4bd19f84acf5c04a4c59e4ace9a89a0c5834df63773,
  bn5.take 6++unpack 11 0x494994e4908d4c4d15a4e4dda69e4a0a5504a0e5d24c539f24a8e5aa4ace1a44acf5c040cc6e5a,unpack 18 0x25062c424846a624a4ca5276e559266a12024a54b225e970d2567adf25e8ceb24c58be2587ae1434a8d9b2160ca83535c210a,unpack 18 0x24846a624a4ca52587ee5278e35925678ed24a5aba26ab12a1b4bd1a044ace1a44a8e1a24a4d19c49ce1a4065418755b8bbd6,unpack 19 0x2547ee824a4ca52484ea426aad27274df6024a5aba24e509c268bf3d24c54b7260910a434ace5a64a0c58849ce1a62a0c38b5712d1bf,unpack 19 0x494994a4909d4849499484e5bec24d9767849ca1384a4edbe4c53a2a49cb9644bd16044b0fdaa4a8d5b0494d1924b4e19a061c583596f97d7,big.take 6++unpack 14 0x4bd3a244909d4849499484b501ac4e1b6fa4c51dcc498a56e4b9220c4b519d24a8dda24acedb24b4f5e0498dda24befef9f,bie.take 6++unpack 14 0x49cc5804949948494a1284cd525a4edbabc4a4cda2494a9404cd6a884a4cd844b919d44a0b9964b109bc4a4d1ae4ef9131e,bfm.take 6++unpack 15 0x4cd7a764949948494a12849091544f1bad24dd8e92494a940490a57e4e1928e498a96e4c129fc49cb5644acfdac4a8e1c05155d936,
  bfj.take 6++unpack 15 0x4acf5f0494a12849091544acfdc44f1b2c44c5421c490a57e4acf1ac4cd4a5049cc1604c11e004a0dd8e4a8e1ae4a8edc853b2e7ab,bbb.take 6++unpack 16 0x4e1b6c8494a128490915449091604cd5e244f1bece4a4e9d0498a96e4c129f44bd29fa498a9544bd29fc4b509ec4a4c98249cd5c455b95afb,bbc.take 6++unpack 16 0x25e971e24848aa24848b02484a9f278e75e270d16424c54b724e5893266b13025674de25470d02587af025882dd25072dd2158162113,b5o.take 7++unpack 16 0x511de60474ade248c81a2490953e4b105ac4f5beda4c5624c49ca546498a96e4e1a2ae498a96e4b515d44a8d9a04b0fdda4a8ed8458160401,b4s.take 6++unpack 17 0x4d95a26434ddbe48469de49899324cd62504f1d2704ad020a4989d8c4a4edbe4d55e5e494a96e4c94606498a9524b0fdda4a4e9d24a8c9705d25b7cb,b1k.take 6++unpack 17 0x2945919dc47c79ca488917e4f5d26e4f9f63449095f049085c64c52df44b12e0849ca1a44c535f4498bd5c4b4f9e24a8e9a44a4c99e5f827de2,b1q.take 7++unpack 16 0x294c531fa424b9b84ace9f250dde2453d521c424ddd24887df64d991d04a0de3249095a64c536224a8cdb449cd1c64b4f1905ed5acd1,b1w.take 7++unpack 16 0xa48a1e7cdb272ab1229eb51c1143509c848489b64fdda0e48899e04a4ce0c4b501ee4a8f1d6494adcc4acddca613272e9,
  b22.take 7++unpack 16 0x524527417093e5d9288914bd15d64452df25493a0241901d44b509c04a4c61e4b501f0490b1ea4acddcc64e8be11,b28.take 7++unpack 16 0x29224549122a489142d0dc64c94a18488b58c4b501f04a0c1fc494cde266efb345,b2h.take 7++unpack 16 0x29224549122a48914c11de04cd4a184151d684b506104a0c9dc494c60269f958a8,b2p.take 7++unpack 16 0xa489152448a922454914b0f5b243961f04a5059a498c20a6e05ae3a,b2u.take 7++unpack 16 0x52448a9224549122a48914bd19da4354df0498fd7271bbdc50,b32.take 8++unpack 15 0x29224549122a489152448a94c129ee7cd68d73,b11.take 7++unpack 16 0x149122a489152448a922454914c129ee82e981f3,b12.take 6++unpack 17 0xa489152448a9224549122a48914c525ec89529dea,
  b0o.take 5++unpack 18 0x52448a9224549122a489152448a94a125ea8cb3e309,b66,b63,b68,b6b,[],[]]
def boxes (r : ℕ) : List FadicGate.Entry :=
  if r < 17 then [] else boxesTape.getD (r-17) []

def plain : ℕ → ℕ × ℕ × ℕ
  | 70 => (3914, 1630, 408)
  | 71 => (3980, 1650, 420)
  | _ => (0,0,0)

private def powersTape : List String := [
  "","","","","","","","",
  "","","","","","","","",
  "","!#","!#&","!#&+","!#&+",z3r,z2Q,z4F,
  "!#%)-8>",z41,z5l,z3q,"!#%(,4<DJ",z49,z6L,z40,
  z69,z4M,z3y,z3x,"!#$&*.48BOUUw~#!","!#$'*/29CIWUo~#&~#!","!#$'*/39DCYWf~#*~#&~#!",z5p,
  "!#$&),4;AFTZYv~#-~#*~#&",z3K,z3u,z31,z5P,z2u,("!#$%(," ++ zz96),z2g,
  z2s,"!!#%(,/47@NMYigm~#0~#E~#A~#=~#9~##","!!#%(*/38@INSjig~#(~#H~#E~#A~#=~#/","!!#%(+/38AEONlji}~#@~#H~#E~#@~#;~##","!!#%'+/39BAQOflju~#8~#L~#H~#E~#?~#/","!!#%'+049CBRQ`nlm~#0~#P~#L~#H~#?~#1",(zz75 ++ "#P~#L~#?~#1"),(zz103 ++ "my~#@~#T~#M~#?~#1"),
  "!!#%'*.17:DITSlrmh~#3~#X~#M~#?~#1","!!#%'*.15;EDUSesmh~!~~#I~#M~#?~#1","!!#%'*.15;FEVS[smhk~#7~#M~#?~#1","!!#%'*.15<FEVSQsmhb~#%~#M~#?~#1","!!#$&),16<BEPSPimhbo~#;~#?~#1","!!#$&),26==EISP`mhb]~#(~#?~#1","!!#$'),26=;ECSPUmhb]s~#?~#1","!!#$'),/68;ECSPNmhb]a~#-~#1",
  "!!#$&)-/35;ECSPNdhb]Vw~#1","!!#$&(-/15;ECMPNYhb]Ve~#1","!!#$&(+/15;@CFPNPhb]VR{","!!#$&(+/15;;CAPNKhb]VQi","!!#$&(+/15;:CAPNK^b]VQV","",""]

def powers (r : ℕ) : List ℕ :=
  if r=0 then [] else KoalaSplitGateWords.powers (powersTape.getD (r-1) "")

private def plainPowers : ℕ → List ℕ
  | 70 => [0, 0, 1, 2, 3, 6, 8, 12, 15, 18, 24, 23, 32, 30, 45, 42, 39, 47, 61, 55, 50, 44, 39, 68, 72, 57, 43, 29, 15]
  | 71 => [0, 0, 1, 2, 4, 5, 8, 10, 15, 19, 21, 24, 33, 31, 39, 43, 40, 40, 63, 58, 52, 47, 41, 55, 77, 63, 49, 35, 20, 6]
  | _ => []

def tailPowers : List ℕ := KoalaSplitGateWords.powers "!!#$&'+,154:CACNKHb]VQLHqcTF7)"

def priced (r:ℕ):Bool:=rowCheck gate r (boxes r) (powers r) (plain r) (plainPowers r)
private theorem priced_list : (List.range 71).all (fun i => priced (i+1)) = true := by decide +kernel

theorem prices {r : ℕ} (hr : 0 < r) (hR : r < terminal) : priced r = true :=
  price hr hR priced_list

theorem tail:plainCheck gate terminal (4012,1650,550) tailPowers=true:=by decide +kernel

private abbrev Chunk (i n v : ℕ) := lossChunk 12 envelope plain boxes i n = v
private theorem checkPart (i n v : ℕ) (ok : Chunk i n v := by decide +kernel) : Chunk i n v := ok
private def part0 := checkPart 0 6 0x2384dc4cc14
private def part1 := checkPart 6 6 0x2384dc4cc14
private def part2 := checkPart 12 6 0x237dcb0caf2
private def part3 := checkPart 18 6 0x231f4cdd529
private def part4 := checkPart 24 6 0x224cc016644
private def part5 := checkPart 30 6 0x20c0fdad09a
private def part6 := checkPart 36 6 0x1e051da14ba
private def part7 := checkPart 42 6 0x19c9ed7a881
private def part8 := checkPart 48 6 0x138557dedd8
private def part9 := checkPart 54 6 0xbca285cac3
private def part10 := checkPart 60 6 0x57cdd5c4dd
private def part11 := checkPart 66 5 0x1d0030976c

theorem loss_bound (N : ℕ) : Bound envelope terminal plain boxes 20830585110848 N :=
  loss_of_chunks 12 envelope terminal plain boxes 20830585110848 N (by decide) (by decide)
    (LossSum.empty _ _ _ _
      |>.append 6 0x2384dc4cc14 part0 |>.append 6 0x2384dc4cc14 part1 |>.append 6 0x237dcb0caf2 part2 |>.append 6 0x231f4cdd529 part3
      |>.append 6 0x224cc016644 part4 |>.append 6 0x20c0fdad09a part5 |>.append 6 0x1e051da14ba part6 |>.append 6 0x19c9ed7a881 part7
      |>.append 6 0x138557dedd8 part8 |>.append 6 0xbca285cac3 part9 |>.append 6 0x57cdd5c4dd part10 |>.append 5 0x1d0030976c part11)

def receipt : KoalaSplitProof.Receipt envelope split unit :=
  ⟨terminal, plain, boxes, powers, plainPowers, tailPowers, 20830585110848,
    by decide,by decide,loss_bound,fun _ h h' => prices h h', tail⟩

end KoalaAt2428Gate21

#print axioms KoalaAt2428Gate21.loss_bound
#print axioms KoalaAt2428Gate21.receipt
