import ProximityPrize.SubmissionLower.KoalaAt2428Gate22
import ProximityPrize.SubmissionLower.KoalaGateSharedData
import ProximityPrize.SubmissionLower.KoalaGateChunkSums
import ProximityPrize.SubmissionLower.KoalaSplitGateWords

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000

set_option linter.defProp false

namespace KoalaAt2428Gate23
open KoalaGateSharedData
open FadicGate KoalaGateCheck
open KoalaWeightedRate (Envelope)
open KoalaFarBridge (rowCheck plainCheck)

def envelope : Envelope :=
  ⟨137,56,8,137,56,3562,4437,⟨9088935216,43020867106,55637901642⟩,3959264156961⟩
abbrev split:ℕ:=64
abbrev unit:ℕ:=1919967861120
abbrev terminal:ℕ:=72
abbrev gate:=KoalaSplitRow.rate envelope split unit

private def boxesTape : List (List Entry) := [
  b05l,b04u,b03z,b033,b022,b023,b00w.take 5++unpack 1 0x1b5650eb,unpack 6 0x4b91dcc429c1832c8c6fde,
  unpack 7 0x254a8e598729c19b2e930e7a,unpack 8 0x25c910c474a8dd8a729cd8730efa946,bxc.take 6++unpack 3 0x490a9844c531fa21bfef11,bwd.take 6++unpack 3 0x4b4e1a44a8f9c423c64571,bwn.take 6++unpack 4 0x4a8e1924bd220449cb98425cc9bd2,but.take 6++unpack 4 0x498ad3e4c12e4a4a8e58e292ca2be,buf.take 7++unpack 4 0x4c54e10490a18a4c93a1c27d3009d,btf.take 6++unpack 5 0x4a4f5d44ace5984b509d24b4f9e82e3c736a,
  bt2.take 7++unpack 4 0x498ad444c126104a4cd922c362b84,brf.take 7++unpack 5 0x262b125694c54a5a49cad502e92c635,bqc.take 6++unpack 6 0x4c111b2498a56e4c9523c4a4e5ac4a8d1ac34fc55fb,bqh.take 6++unpack 7 0x4e9baae4a0bd8e4a4e9b24b916024b909e04a4dd8c38060a12,bpw.take 8++unpack 6 0x4c5465c4e5865c48ca57e4c125ee4acf1a4329fc9a9,bpe.take 8++unpack 7 0x24a4aa5270d966260951024c56a226ab5272334a6200a,bnv.take 8++unpack 8 0x494954a4acfdb24edb2c44a0d9ba4a0a1504cd726e49cb55c3702d7a9,bo3.take 7++unpack 10 0x494954a49095564cd52424dda2984a0a1504a0e9d64c93df44a0cd904b0f1b23dc2ba38,
  bll.take 7++unpack 10 0x490955649095424edbea44cd4244494ad664bd26104acf5be4b911c849cbd8e3fc92d88,bmi.take 8++unpack 10 0x490955649095424b0f5c44edbea24b0f9e8490ad684d5625849cc15e4bd1a063fc92d88,bk3.take 8++unpack 10 0x49095424949d4a4cd4e3e4edbab8490b5764a0a9464d17a70498a96e4bd160641cf7574,bk2.take 8++unpack 11 0x2484aa124a4ea524a4ca5272dd5f268b53225054a325278e0262990f034bd1606442c3b8c,bj8.take 8++unpack 11 0x24a4ea524a4ca52587ed2270d97b2628ee7234b922104b511c44a8dda24acedb44632bd39,bjm.take 9++unpack 11 0x4a0c582494994a494a1284cd52564e9b2b64a4d1a4494a9404cd627e4a4cd844b919d645dc5be8,bfm.take 8++unpack 12 0x24a4ca524a50942484eb1276d35b26ec94c24a54a024852c0270c541234c129fe49cb9644aec1e1c,bfj.take 8++unpack 13 0x4b0fdfc494a1284909d624acf9bc4edaec04c53a12490a5804ace9a04cd4a5249cc1604c122024a0dd8e4d9f9c48,
  bcw.take 9++unpack 12 0x24a50942484eb124844ab268b315274d55e25276e9234c121e64bd29fc498ad544bd29fe4c9c69dd,bdc.take 9++unpack 13 0x25e9b2a2484abb24844ab24a4ea5276dd5126ed366234a0b5264c95a544ace9bc4a4d1904b505f44ef904a9,b6t.take 10++unpack 12 0x23e630424438dc24a4ea525880d3276d764262b32825054a324a4eb0270d358234b515d64df60c0e,b4s.take 9++unpack 14 0x1aa2286ff24034f224c4aa7264ad2627ae724256831624a48bf25276df26ab13124a54b72629cfb03535c4c6e,b1k.take 9++unpack 14 0x1aa329f0424044f324244cd27ae72427af30f2484b0224842ea26090f325a9f0d494c539f6498bd5c5562eb09,b4v.take 9++unpack 14 0x1a99430e1f04ace5ee505ce1253d4a12424ddd84887e144d995d24a0de3449095a84c53a244a4bda2586c2b8b,b1w.take 8++unpack 15 0xd4ca2494f8274a9102969f041943d21e848899e64f9d20048899e24a0bdfc4b912024a8f1d8494a9c85e2923f2,b22.take 12++unpack 11 0x6a652a4a7c13b54880c994c52df844531f65452df441901ee545f6f87,
  b29.take 8++unpack 15 0x353265a9932d4c994352df44c53a08488b59c4b501f24a0c1fc6595804a,b2h.take 8++unpack 15 0x1a9932d4c996a64ca6296fa134192d924b506124a0cddc689f50f9,b0y.take 8++unpack 15 0xd4c996a64cb53265a994b0f5b443d721a4a5099a6c557f0f,b0z.take 8++unpack 15 0x6a64cb53265a9932d4c994bd19dc4354e026fb4566a,b10.take 8++unpack 15 0x353265a9932d4c996a64cb54c129f07cd68d6b,b11.take 7++unpack 16 0x1a9932d4c996a64cb53265a994b915d8823ccdc4,b12.take 6++unpack 17 0xd4c996a64cb53265a9932d4c994c525ee89529de4,b0o.take 5++unpack 18 0x6a64cb53265a9932d4c996a64cb54a125ee8cb3e305,
  b65,b62,b67,b6a,[],[]]
def boxes (r : ℕ) : List FadicGate.Entry :=
  if r < 18 then [] else boxesTape.getD (r-18) []

def plain : ℕ → ℕ × ℕ × ℕ
  | 70 => (3914, 1630, 408)
  | 71 => (3980, 1650, 420)
  | _ => (0,0,0)

private def powersTape : List String := [
  "","","","","","","","",
  "","","","","","","","",
  "","","!#","!#'","!#&,","!#&*0","!#&*0","!#&*18",
  "!#%)-9","!#%).49","!#%).3:H","!#%(/3;JH","!#%(,4<DJ","!#%),5=>LO","!#%(-19=NL","!#%(-06>PN`",
  "!#%(+16@JPW","!#%'+17ADRP","!#$'+28BATRh","!#$',.9=BVT`","!#$'*/49CPVWx","!#$'*/39DJXVp~#'","!#$'*/3:EDZXh~#+~#'","!#$&+04;FE[Z`~##~#+~#'",
  "!#$&)-5;AFU[Zx~#/~#+~#'","!#$')-5<=GO^[o~#2~#/~#+",z5h,"!#$&*.16=JIb`_~#!~#7~#2~#/","!#$&).16>KJ[b`w~#:~#7~#2~#/","!#$&),27>FKUdbo~#2~#:~#7~#2","!#$&),27?ALOfdg~#*~#>~#:~#7~#0","!#$&),28@?MLhfd~#!~#B~#>~#:~#7",
  "!#$%(,/8<@NMbhfw~#:~#B~#>~#:~#0","!#$&(-/58AON[jho~#2~#F~#B~#>~#:",z4Y,"!#$%(+049BFQOnlj~#!~#B~#J~#F~#B~#;","!#$%(+04:CBRQgnlv~#:~#N~#J~#F~#>~#0","!#$%(+04:DCSRaonn~#1~#R~#N~#I~#>~#0","!##%(,.5;?DTSZqon~#)~#I~#R~#L~#>~#0","!##%(*.5;;DOTTsqnz~#A~#U~#L~#>~#0",
  "!##%'*.28;EJUTmsni~#3~#Y~#L~#>~#0","!##%'*.15<FEVTftni~!~~#H~#L~#>~#0","!##%'+/26<FFWT]tnil~#6~#L~#>~#0","!##%'+/26=GFXTRtnic~#$~#L~#>~#0","!##%')-27=CFQTQjnico~#:~#>~#0","!##%'*-27>>FJTQanic^~#(~#>~#0","!##%'*-37><FDTQVnic^s~#>~#0","!##%'*-079<FDTQNnic^a~#,~#0",
  "!!#%&*-/46<FDTQNeic^Ww~#0","!!#%')-/26<FDNQNZic^We~#0","!!#$')+/26<ADGQNQic^WR{","!!#%')+/26<<DBQNKic^WQi","!!#%&)+/26<;DBQNK_c^WQV","",""]

def powers (r : ℕ) : List ℕ :=
  if r=0 then [] else KoalaSplitGateWords.powers (powersTape.getD (r-1) "")

private def plainPowers : ℕ → List ℕ
  | 70 => [0, 0, 1, 2, 4, 6, 9, 13, 15, 19, 25, 24, 33, 31, 46, 43, 40, 48, 62, 56, 50, 45, 39, 67, 71, 57, 43, 28, 14]
  | 71 => [0, 0, 1, 2, 4, 6, 9, 10, 16, 20, 22, 25, 34, 32, 41, 44, 41, 41, 64, 58, 53, 47, 41, 55, 77, 62, 48, 34, 20, 6]
  | _ => []

def tailPowers : List ℕ := KoalaSplitGateWords.powers "!!#$&(+-265;DBDNKHc^WQLHpbSE7("

def priced (r:ℕ):Bool:=rowCheck gate r (boxes r) (powers r) (plain r) (plainPowers r)
private theorem priced_list : (List.range 71).all (fun i => priced (i+1)) = true := by decide +kernel

theorem prices {r : ℕ} (hr : 0 < r) (hR : r < terminal) : priced r = true :=
  price hr hR priced_list

theorem tail:plainCheck gate terminal (4012,1650,550) tailPowers=true:=by decide +kernel

private abbrev Chunk (i n v : ℕ) := lossChunk 12 envelope plain boxes i n = v
private theorem checkPart (i n v : ℕ) (ok : Chunk i n v := by decide +kernel) : Chunk i n v := ok
private def part0 := checkPart 0 6 0x2384dc4cc14
private def part1 := checkPart 6 6 0x2384dc4cc14
private def part2 := checkPart 12 6 0x2382352d39e
private def part3 := checkPart 18 6 0x2325078549d
private def part4 := checkPart 24 6 0x224bfd8c586
private def part5 := checkPart 30 6 0x20bba56f858
private def part6 := checkPart 36 6 0x1dfd4bfdafa
private def part7 := checkPart 42 6 0x19aec5d4d7c
private def part8 := checkPart 48 6 0x1355edcb412
private def part9 := checkPart 54 6 0xba5d144fdd
private def part10 := checkPart 60 6 0x57648d165b
private def part11 := checkPart 66 5 0x1cd8cf6659

theorem loss_bound (N : ℕ) : Bound envelope terminal plain boxes 20797371393882 N :=
  loss_of_chunks 12 envelope terminal plain boxes 20797371393882 N (by decide) (by decide)
    (LossSum.empty _ _ _ _
      |>.append 6 0x2384dc4cc14 part0 |>.append 6 0x2384dc4cc14 part1 |>.append 6 0x2382352d39e part2 |>.append 6 0x2325078549d part3
      |>.append 6 0x224bfd8c586 part4 |>.append 6 0x20bba56f858 part5 |>.append 6 0x1dfd4bfdafa part6 |>.append 6 0x19aec5d4d7c part7
      |>.append 6 0x1355edcb412 part8 |>.append 6 0xba5d144fdd part9 |>.append 6 0x57648d165b part10 |>.append 5 0x1cd8cf6659 part11)

def receipt : KoalaSplitProof.Receipt envelope split unit :=
  ⟨terminal, plain, boxes, powers, plainPowers, tailPowers, 20797371393882,
    by decide,by decide,loss_bound,fun _ h h' => prices h h', tail⟩

end KoalaAt2428Gate23

#print axioms KoalaAt2428Gate23.loss_bound
#print axioms KoalaAt2428Gate23.receipt
