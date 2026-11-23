import ProximityPrize.SubmissionLower.KoalaAt2428Gate18
import ProximityPrize.SubmissionLower.KoalaGateSharedData
import ProximityPrize.SubmissionLower.KoalaGateChunkSums
import ProximityPrize.SubmissionLower.KoalaSplitGateWords

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000

set_option linter.defProp false

namespace KoalaAt2428Gate19
open KoalaGateSharedData
open FadicGate KoalaGateCheck
open KoalaWeightedRate (Envelope)
open KoalaFarBridge (rowCheck plainCheck)

def envelope : Envelope :=
  ⟨135,56,12,135,56,3510,4435,⟨10217526890,54417593335,12920241903⟩,4409637700006⟩
abbrev split:ℕ:=64
abbrev unit:ℕ:=1919968577280
abbrev terminal:ℕ:=72
abbrev gate:=KoalaSplitRow.rate envelope split unit

private def boxesTape : List (List Entry) := [
  unpack 1 0x81984ca,unpack 2 0x4a4cd8e0a1ff81a,unpack 3 0x4a8ddba4a0c97a0c7cbe32,unpack 3 0x4acedae4a4c97c0ed9844a,unpack 4 0x4acedb04a8dd8e49cc19010dff79a,b02g,b02h,b018,
  b019,b01a,b008,byz,bxp,bxq,bw3,bw4,
  unpack 11 0x49495484acfdb84d15e4c4a4e1d64ace9b04b925d64a8d5b04a4d19c4a0c97c4a0c5722c8c6fde,unpack 11 0x49099324d162564b101de4bd2a244a4dd9c4acf5b04ace19e4a4d9a84a0c17249cc96a2e930e7a,unpack 12 0x4a0c982490953e4f1c6ee498b9524bd2a264acf1ca4a8e99a4a8dd9e4a8ddaa49cc5684a0b99430efa946,bt9,unpack 13 0x4b101ca49095444d156644b5320e4b4e9aa4ad01d24b0f5d64b101ac4a8d5b44a0d58c4a0c1724a0c57435a93576,unpack 13 0x49095444908d524edc6de4a4e1944c12e1649cb5804b101c24b501e24a4d57e4a4dd984a0c1744a0b9943805d042,unpack 14 0x4c13a184908d524b105b44e1a2be498a93c4c53a5a4a8e5884acfdce4a8d1a64a8e1984a4d58c4a0b99249cc96e3a0c6ede,unpack 14 0x49cbd8c4909d2c4d15e644c9561e4909d824cd4a2e4b105b84acf1b64a0c9944ace1a04a4c9ac49cc96c4a0c5763c6934f6,
  unpack 15 0x4d16a744909d2c490914e4f5cae24a4f5d44b0eda64b50dd44b505fa4a8e5964ace1b44a4d9a24a0d17a4a0c5744a0b9963ec5cfc2,unpack 15 0x2567ee124848a725a7ee7272e17424a54a0262970c25064c725c8aed25472d625878de2526cd225062ba25262d203412295da,unpack 16 0x270d55524848a724a4aa2266b32c266b72d25056a7262a52c2525caf25684e925672ec2567cc42546edd25262d225062bb0b427cabc3,unpack 16 0x25e990d24a4aa22484ca2274e37a26090e424c4eaf268b32c25070d625468d425a86e92506ac72566ede25268c324a60c40d4585fa8e,unpack 17 0x272d96425060bf2484ca22587ae3278e9662505ec425274db25e910825c86f325270cb2566edc25272cd2546acd24c64cb25468af0747e2955a,unpack 17 0x268b5342484ca22484c9e264a936274cd3924650bc26096fd2567ad625c88f425672d625268d625474cd24e66d62566cb62505ecc034a3f5b72,unpack 18 0x272d9632587ee72484c9e24848a1274e576262991424a54a026cbd3324c52b625a8ce425a72f125070c325670d12526cc925262d425064bc0b4b99715b,unpack 18 0x270d35b2484c9e24848a125880df278e16d25070de25052ac268bd3d24e58ac25c8af925678de25268d625672d125472d325062bc24a62c5034df63773,
  unpack 19 0x272d9632609d0a24848a124846a7268b32c270d95725052ac25272e6264a3032526acc25676d725478de25a80e82546ad725268c424a60c425064bd1550ff5af2,unpack 19 0x270d95d25060c224846a72484ca227ae961266a92c24a50aa2609d1625678dc25c8ae824e5cc42567ae025a82dc2546ad724a60c42506ac525662c003535c210a,unpack 20 0x272d963268b73024846a72484ca225a7ce4278eb642587aef24854b226cbb3924e5ead25e8f0625470d125674d82546ed424c66c825272ce25460bf25264bd0755b8bbd6,unpack 20 0x274d5662547ce52484ca2248469d26ab32c278e96e24854b225058a826ac13e24c58bd25e8f072587cd325672d225268cc24a66c82586ed125064bd2525ecd0b5712d1bf,unpack 21 0x272d963270cf5c2484ca2248469d24a4ca1274e96f26cbb3c25058a825272db264a72024c54a925e910725a82dc25670df24a66c82586ecb2526ac62505ecc24c62c703596f97d7,unpack 21 0x274d56625c9b0c248469d24a4ca125a82da272e18226498f724c50b525c950925a88e625674d72567adf25a78ee24c6ed025c76df25068b425264d624a62c625264be155c78bb56,unpack 22 0x1396cb19396cb39272d5c9252650925284c134579993c74b690a4a549e266b74625264c125c90ef25260d22567ed42546cde25278e525664bb24c68d025064bd25662c1035ed5816e,unpack 22 0x274d566264b32e24a4ca124a509824648a727ae573272cf5624a549e24650be272cb4924c5abd262970424c54a825884dd2546ede25278e625060c42526cc725460c125266be1d6085bed3,
  unpack 23 0x272d963276db5825476ee24a509824648a72587ee127ae775264a31124650be25876d3266af3324c58a7262930525274ce25266cc25884f625262ac2506ee625460c025064bd24e62cc1b628c5d6f,unpack 23 0x274d56626ed15424a509824648a724846ad268b51a27ae57125278ed24a4ead26296fd25e990324c58ad26092ff25a82f32546cc92506eeb25462b025470d925064bd24c60cb25068bb0d6595ac3a,unpack 24 0x272d963276db5625e990d24648a724846ad24a4ca1278e75f272df7824a4ead2525c9a266b93b25472d825468c925c870025882db25070db25262ce25a76d725064bd24c60cb24e66ba2566ab20767f24706,unpack 24 0x13a6cac943749611e2b769221f5c925265092c416b93d6fb79315b979292c5492426569396fb3126275812e477892a366712c3d7592b3e65127336d92d386b9263065928376286a5260cf036a4f0d1e,unpack 25 0x1396dac154719a9375c9190a26589211b6f9252548933589593e78a712c427e92526621293a6d9365c9d925295a9335485126295412d427a128397392b366112a3870927335d12b385e83a5266bf0b6ba92307,unpack 25 0x2a4df42270bf292649afd21c52a523c36d624444a927cf35027efd2724850eb24842df26298fe25a9b0a24e4ecf264a10124a5cad25c82f92567ad725266d224e68d225870bd25268da24e5cb224c64c9076e05bdd3,unpack 26 0x541b6964d14e18127d27325d109246112b3b7a9447f9595360961072d601211c78137687a128378b12424689314f8b92a326b928387612d3c6392b3b6d928345a12a336d12937651263264838d710f0c9e,unpack 26 0xf89127d2c406f10a295193b5b9115672ab9314c7d1083256921216b9417b8a1222576928338192e427f92a3c741252b7212b367212b3c6d92a376c929346092532641293068069d72bf4a03,
  unpack 27 0x93e2449f128f12a70a33b58499a9424252a356190f436b9555b97102315b12f4878929318612d3f7b1242c7992b36721242f7a12d3b699263164128306792b35598e9575c86d82,unpack 27 0x93e2449f1224f891298243c8c5335285107345813251851222c6212d407b1293383925337792a2e79924307a9292f6792a355992731668a8b7722836b,unpack 27 0x24f89127c4893e2449f12252c3b699345689901394512d4183129367b926317f92628779272e7e12a3176126316612b32620583797f4983,unpack 27 0x93e2449f1224f89127c4893e2529356190b4e6c12941661262f8192629779252c8292a2f7e1262e6e1262f6d01957c886d02,unpack 27 0x49f1224f89127c4893e2449f12252e417090845669263e5c1272f789262b8a126287b9262b76926306d24837ee5331a,unpack 27 0x24f89127c4893e2449f1224f89127d2e4575902405792a42691242782126287d9242a7b1272c772d838141f932,unpack 27 0x24f89127c4893e2449f1224f89127c4a5c8aea20c88b124270ce24c50fb2484f0625256f13b488ad92829c3a67,unpack 27 0x93e2449f1224f89127c4893e2449f12252f44740fd49451282b7f125297d1262a7d1dc185a58932,
  unpack 27 0x49f1224f89127c4893e2449f1224f89127d264473904464112527851262a7d1dc188af2e95,unpack 27 0x24f89127c4893e2449f1224f89127c4893e250449719243a4612428839dc18bb8d3f8,bq,bs,bt,[],[]]
def boxes (r : ℕ) : List FadicGate.Entry :=
  if r < 9 then [] else boxesTape.getD (r-9) []

def plain : ℕ → ℕ × ℕ × ℕ
  | 70 => (3914, 1630, 408)
  | 71 => (3980, 1650, 420)
  | _ => (0,0,0)

private def powersTape : List String := [
  "","","","","","","","",
  "","!%","!$)","!$*","!$(.","!$)/5","!$'07","!$(,9A",
  "!$'-39","!#'-2;","!#&+3=H","!#'+4?@T","!#&,/9?XT","!#&*05APX","!#&*07CH]X","!#&*18ECa]",
  "!#%)-9?EXa]","!#%).49FPea","!#%).3:HHie^","!#%(/3;JHaie","!#%(,4<DJWmi^","!#%),5=>LOqmi","!#%(-18=NLhqm^","!#%(-06?PN`tqj",
  "!#%(+16@JPWxtq^","!#%'+17ADRPpxtj","!#$',28BATRh|xt^","!#$',.9=BVT`~##|xj","!#$'*/49CPVWx~##|u^","!#$'*/39DIXVp~#'~##|j","!#$'*/4:EDZXh~#+~#'~##u^","!#$&+04;FE[Z_~##~#+~#'~##j",
  "!#$&)-5;AFU[Zx~#/~#+~#'u^","!#$')-5<=GO^[o~#3~#/~#+~#$j","!#$&*.28<II`^g~#*~#3~#/~#+u^","!#$&*.16=JIb`_~#!~#6~#3~#/~#$j","!#$&).16>KJ[b`w~#:~#6~#3~#/u^","!#$&),27>FKUdbo~#2~#:~#6~#3~#$j","!#$&),27?ALOfdg~#*~#>~#:~#6~#0u^","!#$&),28@?MLhfd~#!~#B~#>~#:~#6~#$j",
  "!#$&(-/8<@NMbhfw~#:~#B~#>~#:~#0u^","!#$&(-/58AON[jho~#2~#F~#B~#>~#:~#$j","!#$&(+039AJOUljh~#*~#J~#F~#B~#>~#0u^","!#$%(+049BFPOmlj~!~~#B~#J~#F~#B~#;~#$j","!#$%(+04:CBQPgmlv~#9~#M~#J~#F~#B~#0u^","!#$%(+04:DCSRaonn~#1~#Q~#M~#J~#F~#7~#$i","!##%(,.5;?DTSZqon~#)~#I~#Q~#N~#F~#7~#(u^","!##%(*.5;;DOTTsqo~!~~#A~#U~#Q~#F~#7~#(vg",
  "!##%'*.28;EJUTmspm~#9~#Y~#U~#F~#7~#(vgW","!##%'*.16<FEVUgupk~#'~#Q~#U~#F~#7~#(vgW","!##%'+/26<GFWU^vpkq~#>~#U~#F~#7~#(vgW","!##%'+/26=GFXUSvpke~#+~#U~#F~#7~#(vgW","!##%')-27=CFRURlpkeu~#B~#F~#7~#(vgW","!##%'*-27>>FKURbpkeb~#/~#F~#7~#(vgW","!##%'*-37><FDURXpke_y~#F~#7~#(vgW","!##%'*-079<FDUROpke_f~#3~#7~#(vgW",
  "!!#%'*-/46<FDUROfke_Y}~#7~#(vgW","!!#%')-/26<FDNRO]ke_Yj~#7~#(vgW","!!#$')+/26<ADHRORke_YV~#$~#(vgW","!!#%')+/26<<DBROLke_YSn~#(vgW","!!#%&)+/26<;DBROLae_YSZ~#(vgW","",""]

def powers (r : ℕ) : List ℕ :=
  if r=0 then [] else KoalaSplitGateWords.powers (powersTape.getD (r-1) "")

private def plainPowers : ℕ → List ℕ
  | 70 => [0, 0, 1, 2, 4, 7, 9, 13, 16, 20, 26, 24, 33, 31, 46, 43, 40, 49, 63, 57, 52, 46, 41, 72, 76, 61, 47, 32, 17]
  | 71 => [0, 0, 1, 2, 4, 6, 9, 11, 16, 20, 22, 25, 34, 32, 41, 45, 42, 42, 65, 60, 54, 49, 43, 59, 82, 67, 52, 37, 22, 8]
  | _ => []

def tailPowers : List ℕ := KoalaSplitGateWords.powers "!!#$&(+-265;DBEOLIe_YSMKvgWI:+"

def priced (r:ℕ):Bool:=rowCheck gate r (boxes r) (powers r) (plain r) (plainPowers r)
private theorem priced_list : (List.range 71).all (fun i => priced (i+1)) = true := by decide +kernel

theorem prices {r : ℕ} (hr : 0 < r) (hR : r < terminal) : priced r = true :=
  price hr hR priced_list

theorem tail:plainCheck gate terminal (4012,1650,550) tailPowers=true:=by decide +kernel

private theorem exactLoss0 : lossChunk 1 envelope plain boxes 0 24 = 9721606773038 :=
  by decide +kernel

private theorem exactLoss24 : lossChunk 1 envelope plain boxes 24 24 = 8463083458060 :=
  by decide +kernel

private theorem exactLoss48 : lossChunk 1 envelope plain boxes 48 23 = 2606460589351 :=
  by decide +kernel

theorem loss_bound (N : ℕ) : Bound envelope terminal plain boxes 20791150820449 N :=
  loss_of_chunks 1 envelope terminal plain boxes 20791150820449 N (by decide) (by decide)
    (LossSum.empty _ _ _ _
      |>.append 24 9721606773038 exactLoss0
      |>.append 24 8463083458060 exactLoss24
      |>.append 23 2606460589351 exactLoss48)

def receipt : KoalaSplitProof.Receipt envelope split unit :=
  ⟨terminal, plain, boxes, powers, plainPowers, tailPowers, 20791150820449,
    by decide,by decide,loss_bound,fun _ h h' => prices h h', tail⟩

end KoalaAt2428Gate19

#print axioms KoalaAt2428Gate19.loss_bound
#print axioms KoalaAt2428Gate19.receipt
