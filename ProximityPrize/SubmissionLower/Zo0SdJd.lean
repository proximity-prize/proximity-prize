import ProximityPrize.SubmissionLower.A0
import ProximityPrize.SubmissionLower.P6Defs
set_option Elab.async false
set_option autoImplicit true
namespace P5_7
noncomputable section
open Polynomial
open P5 (K jG p node twist blockLength k)
open cu (L FX vP Shape Jet Equation kr qD jz j9 rD ku triangle slots)
open qQ (zI)
open scoped BigOperators
abbrev midAgreement:ℕ:=179740
abbrev farAgreement:ℕ:=179779
def Qn (lo hi:ℕ) (w:ℤ) :Prop :=(lo:ℤ)≤w∧w≤(hi:ℤ)
def YQ {A u del} (M:jG u del) {Γ} (F:P1.bje A M Γ)
    (H :L[X]) :Prop :=
  let σ:=frobenius L p
  let H' := H.map σ
  H.Monic∧H.natDegree=M.iF.toNat∧H∣j9 M.E ∧
  H'.Monic∧H'.natDegree=M.iF.toNat∧H' ∣ j9 (M.E.map twist) ∧
  IsCoprime H H' ∧
  (∀ i,H.eval (algebraMap K L (node i))≠0∧H'.eval (algebraMap K L (node i))≠0) ∧
  IsCoprime (j9 (M.Q*M.factor*M.A₀)) H ∧
  IsCoprime ((j9 (M.Q*M.factor*M.A₀)).map σ) H' ∧
  ∀ γ∈Γ,
    let z :=algebraMap K L (M.label γ)
    let D:=j9 (M.factor*M.wK γ)
    let S:=j9 (F.scalar γ)
    IsCoprime D H∧IsCoprime (D.map σ) H' ∧
    H∣D *S+C z*j9 M.Q ∧
    H' ∣ D.map σ*S+C (z^p)*(j9 M.Q).map σ
structure HeightPrice where
 lo:ℕ
 hi:ℕ
 cap:ℕ
def RegularBound (A:ℕ) (r :HeightPrice) :Prop :=
  ∀ u del (M:jG u del) Γ (F:P1.bje A M Γ),
    Qn r.lo r.hi M.iF→M.shift∉Γ →
    ∀ H,YQ M F H→Γ.card≤ r.cap
structure Bank where
 shape :Shape
 ad1 :ℕ
 arY:ℕ
structure Ls where
 dI:ℕ
 free :Bank
 moving:Bank
structure NativeWitness where
 g:ℕ
 c:ℕ
 j:ℕ
 W:ℕ
structure jJ where
 seedCap:ℕ
 slots :ℕ
 arY:ℕ
 rate :ℕ
 witness :NativeWitness
structure FarRow where
 lo:ℕ
 hi:ℕ
 prefixFee :ℕ
 RU:List ℕ
 stopReserve :ℕ
 terminal:Bank
 stages :List Ls
 gw:List jJ
inductive FarBand where
 | dbl | lZ | om | wS | vX | vg | wI | vW | wO | wQ
def nearRows :List HeightPrice :=
 [⟨2533,2533,0x392c1c3d1516791⟩,
  ⟨2534, 2534,0x39efe5516db7297⟩,
  ⟨2535,2535,0x399f9528fc660b5⟩,
  ⟨2536,2536,0x38bcf638f5b1ee5⟩,
  ⟨2537,2537,0x39a9bf4e9dda3ed⟩,
  ⟨2538,2538,0x3913a61a2ac3bbb⟩,
  ⟨2539,2541,0x3893b3aace6ab4a⟩,
  ⟨2542,2544,0x378184ad7a0f0dc⟩,
  ⟨2545,2554,0x391b69e46852e9b⟩,
  ⟨2555,2564,0x374e3b542c1b151⟩,
  ⟨2565,2574,0x2c6e14163fdd96c⟩,
  ⟨2575,2580,0x2860ba8838d60bd⟩,
  ⟨2581, 2581,0x263ae40db164e37⟩,
  ⟨2582,2703,0x25cb4eee9204ca3⟩]
def lateRows :List HeightPrice :=
 [⟨2704, 2707,0x25ed9d49dbd1c57⟩,
  ⟨2708,2714,0x2479f82b50d25cf⟩,
  ⟨2715,2724,0x2572582d0e92d12⟩,
  ⟨2725,2749,0x21689afeba26736⟩,
  ⟨2750,2774,0x199d0a4193b2ecc⟩,
  ⟨2775,2799,0x206629dff9bda0e⟩,
  ⟨2800,2899,0x1bb0ecbd53888c7⟩,
  ⟨2900,2918,0xf4dfd628433bef⟩,
  ⟨2919,2945,0xa956692ec8d45c⟩,
  ⟨2946,2949,0x90dcb71fa3d4b8⟩,
  ⟨2950,2979,0x8e476ba74076fd⟩,
  ⟨2980,2999,0x7e898d18aa247f⟩,
  ⟨3000,3049,0x7587968a62f484⟩,
  ⟨3050,3099,0x61f4041aeba36e⟩,
  ⟨3100,3199,0x53c906b2084f94⟩,
  ⟨3200,3399,0x3b7bd3d8532d68⟩,
  ⟨3400,3554,0x1b73ee869636e9⟩,
  ⟨3555, 3599,0x13012855bab6cc⟩]
def FarBand.row:FarBand→FarRow
  | .dbl =>
    ⟨3600,3999,0x3ca5cf09dd2477,[1, 2,3,4,5,6,7,8],0,⟨⟨1360,1890,386,23288⟩,0x41c31b340000,0x1b40a320c92750⟩,[⟨0,⟨⟨50,69,15,283⟩,0xf4600000,0xb41b1b0⟩,⟨⟨122,169,35,2023⟩,0xcb4780000,0xa7fac87fc⟩⟩,
     ⟨1,⟨⟨56,77,17,330⟩,0x156e40000,0x1460c90a⟩,⟨⟨141,196,41, 2316⟩,0x13b5080000,0x15c13fb802⟩⟩,
     ⟨2,⟨⟨58,80,17,405⟩,0x172740000,0x1c6d1f18⟩,⟨⟨148,205,42,2775⟩,0x1657ac0000,0x1eb69fd625⟩⟩,
     ⟨4,⟨⟨73,101, 22,473⟩,0x2e5640000,0x53c57fe4⟩,⟨⟨189,262,55, 3322⟩,0x2f15200000,0x62efb58dc8⟩⟩,
     ⟨5,⟨⟨78,108,23,535⟩,0x376900000,0x79715c18⟩,⟨⟨203,282,58,3618⟩,0x396fe80000,0x8e0d24427c⟩⟩,
     ⟨6,⟨⟨84,116,26,571⟩,0x4764c0000,0xb241ee62⟩,⟨⟨208,289,59,4175⟩,0x3d6a080000,0xb3fc83e744⟩⟩,
     ⟨10,⟨⟨106,147,32,784⟩,0x8b45c0000,0x2621f5e29⟩,⟨⟨267,371,79,5879⟩,0x856c400000,0x2c365815740⟩⟩,
     ⟨16,⟨⟨141,195,44,1074⟩,0x14c4cc0000,0xa41e8fadc⟩,⟨⟨360,500,105,7890⟩,0x14203b40000,0xc07f87498c6⟩⟩,
     ⟨18,⟨⟨124,171,38,2260⟩,0xe00240000,0xcfc0e50f3⟩,⟨⟨282,392,79,240171⟩,0x96abe00000,0x8877ee11ac10⟩⟩,
     ⟨32,⟨⟨239,330,74,1827⟩,0x6338000000,0x8bf95f6f6a⟩,⟨⟨582,808,165,14653⟩,0x52ca42c0000,0x946206be499a⟩⟩],[⟨99,17583,0x1474ab46d1a406,262144,⟨0,0,0,0⟩⟩,
     ⟨96,17833,0x14c0eaa39c182a,2671703,⟨4, 25,4,92181⟩⟩,
     ⟨93,18238,0x153c70019c63ac,4291145,⟨8,27,8,141326⟩⟩,
     ⟨90,18898,0x1605bb1f89e834,6243111,⟨11,30,11,188907⟩⟩,
     ⟨86,19674,0x16f267396ade04,8510525,⟨15, 33,15,235350⟩⟩,
     ⟨81, 21152,0x18b52db1f70160,11087527,⟨19,36,19,281112⟩⟩,
     ⟨74, 23288,0x1b40a320c92750,13949208,⟨25, 39,25, 325683⟩⟩,
     ⟨64, 23288,0x1b40a320c92750,17101287,⟨30,42,30,370139⟩⟩,
     ⟨51, 23288,0x1b40a320c92750,20538481,⟨36,45, 36,414012⟩⟩,
     ⟨36,23288,0x1b40a320c92750,24259247,⟨42,48,42,457582⟩⟩,
     ⟨19,23288,0x1b40a320c92750,28256088,⟨49,51,49,500750⟩⟩,
     ⟨0,23288,0x1b40a320c92750,32527639,⟨55, 54,54,543783⟩⟩]⟩
  | .lZ =>
    ⟨4000,4799,0x974ae5bf3ff06,[1,3,5,7],2,⟨⟨652,908,184,12230⟩,0x73e2d880000,0xc342f2eaf031⟩,[⟨0,⟨⟨37,51,11, 239⟩,0x65900000,49680436⟩,⟨⟨101,140,28,1171⟩,0x715dc0000,0x2cb6ca72e⟩⟩,
     ⟨1,⟨⟨44,61,13,272⟩,0xa6cc0000,0x6a4e2e8⟩,⟨⟨111,154,30,1412⟩,0x930200000,0x4d1b01c01⟩⟩,
     ⟨2,⟨⟨50,69,15, 311⟩,0xf4600000,0xc6d5030⟩,⟨⟨128,178,36,1589⟩,0xe6e380000,0x9e11eafec⟩⟩,
     ⟨4,⟨⟨61,84,18,403⟩,0x1af5c0000,0x225819b4⟩,⟨⟨171, 238,48,1941⟩,0x2207480000,0x25ed7e8340⟩⟩,
     ⟨5,⟨⟨67,93,20,436⟩,0x23c780000,0x376116df⟩,⟨⟨172,239,48,2217⟩,0x2278980000,0x2c0c1f7010⟩⟩,
     ⟨6,⟨⟨67,93,20,538⟩,0x23c780000,0x44ec67f5⟩,⟨⟨180,250,50,2490⟩,0x2751dc0000,0x3b0981d8b6⟩⟩,
     ⟨10,⟨⟨96,133, 30,628⟩,0x6a97c0000,0x150b00fa6⟩,⟨⟨253, 352,70,3215⟩,0x6bfebc0000,0x126a5043c66⟩⟩,
     ⟨18,⟨⟨138,191,43,985⟩,0x1376a80000,0x8a0ebdb5c⟩,⟨⟨352,490,98,5062⟩,0x122a1140000,0x6ce60428abe⟩⟩,
     ⟨32,⟨⟨203,281,63,1763⟩,0x3d1d000000,0x47a6dcbb00⟩,⟨⟨550,766,155,8079⟩,0x45963080000,0x4113741c898a⟩⟩],[⟨73,7343,0x73f3e95cf4f9,262144,⟨0,0,0,0⟩⟩,
     ⟨70,7414,0x751ae18a21b1, 2664439,⟨4, 26,4,93773⟩⟩,
     ⟨67,7575,0x77b7c1605839,4295513,⟨7,28,7,144038⟩⟩,
     ⟨64,7912,0x7d2fd2539c41,6265891,⟨13, 30,13,192646⟩⟩,
     ⟨60,8470,0x863e083872b1,8554379,⟨17,33,17,239929⟩⟩,
     ⟨54,11600,0xb9099d4bab81,11151655,⟨19,37,19,286341⟩⟩,
     ⟨41,12230,0xc342f2eaf031,14038659,⟨25,40,25, 331793⟩⟩,
     ⟨24,12230,0xc342f2eaf031,17221167,⟨32,43, 32,376809⟩⟩,
     ⟨3,12230,0xc342f2eaf031, 20701581,⟨39,46,39,421594⟩⟩]⟩
  | .om =>
    ⟨4800,7744,0x217ebe780d84cc,[],2,⟨⟨492,686,138,6001⟩,0x31af2dc0000,0x1edb97e51b1f⟩,[⟨0,⟨⟨24,33,7,217⟩,0x1d300000,8617392⟩,⟨⟨50,70,13,849⟩,0xdc9c0000,0x20e3dc7d⟩⟩,
     ⟨2,⟨⟨34,47,10,297⟩,0x4f100000,45194787⟩,⟨⟨74,103,20,1117⟩,0x2c8940000,0xc917f44f⟩⟩,
     ⟨5,⟨⟨50,69,15, 396⟩,0xf4600000,0xffadf10⟩,⟨⟨111,155, 30,1509⟩,0x930200000,0x543afe6dd⟩⟩,
     ⟨10,⟨⟨70,97,21,694⟩,0x28d4c0000,0x6a1779b0⟩,⟨⟨155,216,41, 2593⟩,0x184d080000,0x21355d5e2c⟩⟩,
     ⟨18,⟨⟨118,163, 37,829⟩,0xc4b2c0000,0x3e733792a⟩,⟨⟨267,372,72,3348⟩,0x7c56480000,0x17614ae038b⟩⟩,
     ⟨32,⟨⟨182,252,55,1451⟩,0x2b4a500000,0x25602bba58⟩,⟨⟨440,613,121,5239⟩,0x230b5940000,0x10f0504e7cda⟩⟩],[⟨47,4472,0x16cb72995317,262144,⟨0,0,0,0⟩⟩,
     ⟨45,4611,0x178718e6082f,2642622,⟨4, 28,4,100249⟩⟩,
     ⟨43,4882,0x18f4f24d8a67,4305649,⟨9,30,9,153597⟩⟩,
     ⟨40,5303,0x1b2d4b9952cf,6325786,⟨13, 33,13,205212⟩⟩,
     ⟨35,6001,0x1edb97e51b1f,8682759,⟨16,37,16,255514⟩⟩,
     ⟨27,6001,0x1edb97e51b1f,11366214,⟨24,40,24,304918⟩⟩,
     ⟨16,6001,0x1edb97e51b1f,14359113,⟨28,44, 28,353401⟩⟩,
     ⟨4,6001,0x1edb97e51b1f,17682850,⟨31,48,31,401826⟩⟩]⟩
  | .wS =>
    ⟨7745,7999,0x30916459e3a41,[],0,⟨⟨124,173, 32,946⟩,0xc4fd80000,0x4d4721c50⟩,[⟨0,⟨⟨11,15, 3,157⟩,55574528,340020⟩,⟨⟨20,28,4,328⟩,0xdc00000,5498358⟩⟩,
     ⟨2,⟨⟨21, 29,6,169⟩,0x13cc0000,4053098⟩,⟨⟨38,53,9,450⟩,0x5d840000,93084486⟩⟩,
     ⟨5,⟨⟨34,47,10,255⟩,0x4f100000,38604819⟩,⟨⟨64,89,15,693⟩,0x1a3600000,0x3ee0c420⟩⟩,
     ⟨10,⟨⟨54,75,16,422⟩,0x12f140000,0x1733fe83⟩,⟨⟨101,141, 24,1179⟩,0x64f3c0000,0x28e7c6425⟩⟩],[⟨28,903,0x499f1c803,262144,⟨0,0,0,0⟩⟩,
     ⟨26,926,0x4b93c6044, 2641191,⟨4, 28,4,100867⟩⟩,
     ⟨24,946,0x4d4721c50,4308183,⟨9,30,9,154543⟩⟩,
     ⟨21,946,0x4d4721c50,6333811,⟨11,34,11, 206442⟩⟩,
     ⟨17,946,0x4d4721c50,8689391,⟨18,37,18,256691⟩⟩,
     ⟨11,946,0x4d4721c50,11382727,⟨21,41, 21,306462⟩⟩,
     ⟨4,946,0x4d4721c50,14394765,⟨30,44,30,355480⟩⟩]⟩
  | .vX =>
    ⟨8000,14499,0x2a6fcf9a477df,[],0,⟨⟨124,173, 32,946⟩,0xc4fd80000,0x4d4721c50⟩,[⟨0,⟨⟨11,15, 3,125⟩,55574528,269812⟩,⟨⟨20,28,4, 271⟩,0xdc00000,4527648⟩⟩,
     ⟨2,⟨⟨21, 29,6,153⟩,0x13cc0000,3657514⟩,⟨⟨38,53,9,406⟩,0x5d840000,83762646⟩⟩,
     ⟨5,⟨⟨34,47,10,237⟩,0x4f100000,35780547⟩,⟨⟨64,89,15,639⟩,0x1a3600000,0x39d79bc0⟩⟩,
     ⟨10,⟨⟨54,75,16,397⟩,0x12f140000,0x15c71585⟩,⟨⟨101,141, 24,1092⟩,0x64f3c0000,0x25ce98460⟩⟩],[⟨26,846,0x44c657014, 262144,⟨0,0,0,0⟩⟩,
     ⟨25,919,0x4afb65e73,2590123,⟨5, 33,5,114796⟩⟩,
     ⟨23,946,0x4d4721c50,4320503,⟨9,37,9,174923⟩⟩,
     ⟨20,946,0x4d4721c50,6451251,⟨15,41,15,233439⟩⟩,
     ⟨15,946,0x4d4721c50,8953863,⟨21,46,21, 290363⟩⟩,
     ⟨9,946,0x4d4721c50,11822211,⟨27,51, 27,346399⟩⟩,
     ⟨2,946,0x4d4721c50,15048519,⟨33,56,33,401763⟩⟩]⟩
  | .vg =>
    ⟨14500,21447,0x2c8a3f7be2f7,[],0,⟨⟨40,56,8,289⟩,0x60000000,64067472⟩,[⟨0,⟨⟨6,8,1,47⟩,9699328,9840⟩,⟨⟨8,11,1,86⟩,17039360,43769⟩⟩],[⟨18,237,52059840,262144,⟨0,0,0,0⟩⟩,
     ⟨17,263,58063656,2530247,⟨5,41,5,129024⟩⟩,
     ⟨15,289,64067472,4320895,⟨11,47,11,195795⟩⟩,
     ⟨11, 289,64067472,6543511,⟨16,54,16,260633⟩⟩,
     ⟨5,289,64067472,9186957,⟨22,61, 22,324261⟩⟩]⟩
  | .wI =>
    ⟨21448,23999,0x12cd35d01098,[],0,⟨⟨30,42,6,207⟩,0x2a700000,15360513⟩,[⟨0,⟨⟨6,8,1, 21⟩,9699328,4328⟩,⟨⟨8,11,1,36⟩,17039360,17919⟩⟩],[⟨14,164,12035667,262144,⟨0,0,0,0⟩⟩,
     ⟨13,186,13736751, 2505479,⟨5,46,5,133903⟩⟩,
     ⟨10,207,15360513,4316821,⟨12,52,12,203160⟩⟩,
     ⟨5,207,15360513,6571811,⟨17,60,17,270342⟩⟩]⟩
  | .vW =>
    ⟨24000,28299,0x11a38a578eb7,[],0,⟨⟨30,42,6,207⟩,0x2a700000,15360513⟩,[⟨0,⟨⟨6,8,1,19⟩,9699328,3904⟩,⟨⟨8,11,1,32⟩,17039360,15851⟩⟩],[⟨13,159,11649057,262144,⟨0,0,0,0⟩⟩,
     ⟨12,182,13427463,2462235,⟨6,55,6,141935⟩⟩,
     ⟨9,207,15360513,4300707,⟨12,64,12,214909⟩⟩,
     ⟨4, 207,15360513,6603831,⟨19,74,19,285918⟩⟩]⟩
  | .wO =>
    ⟨28300,32410,0x10120ef2b333,[],0,⟨⟨30,42,6,207⟩,0x2a700000,15360513⟩,[⟨0,⟨⟨6,8,1,16⟩,9699328,3268⟩,⟨⟨8,11,1, 27⟩,17039360,13266⟩⟩],[⟨12,156,11417091, 262144,⟨0,0,0,0⟩⟩,
     ⟨11,181,13350141, 2418036,⟨7,68,7,149257⟩⟩,
     ⟨8,207,15360513,4277481,⟨13,81,13,225583⟩⟩,
     ⟨2,207,15360513,6617456,⟨22,94, 22,299960⟩⟩]⟩
  | .wQ =>
    ⟨32411,33657,0x2f3587c9639,[],0,⟨⟨8,11,1,55⟩,17039360,27742⟩,[⟨0,⟨⟨4,5,1,13⟩,4456448,790⟩,⟨⟨5,7,1, 25⟩,6815744,3626⟩⟩],[⟨13,46,23089,262144,⟨0,0,0,0⟩⟩,
     ⟨11,47,23606,2403541,⟨7,74,7,151342⟩⟩,
     ⟨9,55,27742,4267835,⟨15,87,15,228635⟩⟩,
     ⟨3,55,27742,6618541,⟨23,102,23, 304067⟩⟩]⟩
abbrev InFar (b:FarBand) (w:ℤ) := Qn b.row.lo b.row.hi w
abbrev aKj (b:FarBand) :=Fin b.row.gw.length
abbrev Test (b:FarBand) :=Option (aKj b)
abbrev terminal (b:FarBand) :=b.row.terminal
abbrev cV (b:FarBand) (i:aKj b) :=b.row.gw.get i
def dfG (b:FarBand) (i:aKj b) :Bank :=
  ⟨{ (terminal b).shape with U:=(cV b i).slots },
    (terminal b).ad1,(cV b i).arY⟩
def Jr (b:FarBand) (t:Bank) :Prop :=
  t=terminal b∨(∃ s∈b.row.stages,t=s.free∨t=s.moving) ∨
    ∃ i:aKj b,t=dfG b i
def O2 (s :Shape) :=s.m*farAgreement - 1
def anM (h r :ℕ) (s :Shape) :=O2 s - 2*h*r
def j3 (h:ℕ) (t:Bank) :=triangle t.shape.U*t.ad1+2*h*t.arY
def bbk (h:ℕ) (t:Bank) (rows :vP) :Prop :=
  ∀ W<t.shape.m*farAgreement,
    (∀ q≤t.shape.B,∀ j≤ min q t.shape.J,q*(131071-h)≤W+1+j) →
    triangle t.shape.U*ku t.shape (fun q j=>W+1+j - q*(131071-h)) ≤
      j3 h t + ∑ w∈Finset.range (W+1),Module.finrank FX (rows t.shape w)
structure Source (b:FarBand) {u del} (M:jG u del) {Γ}
  (F:P1.bje farAgreement M Γ) (rows :vP) :Prop where
 nested : ∀ t,Jr b t → ∀ t',Jr b t' →
  t.shape.m=t'.shape.m→t.shape.B=t'.shape.B→t.shape.J=t'.shape.J →
  t.shape.U≤t'.shape.U → ∀ W W',W≤W' → rows t.shape W≤ rows t'.shape W'
 necessary : ∀ t,Jr b t → ∀ W<t.shape.m*farAgreement,∀ P∈rows t.shape W,
  ∀ γ∈Γ,rD P (M.label γ) (F.scalar γ)=0
 shape : ∀ t,Jr b t → ∀ W,∀ P∈rows t.shape W,qQ.oU P t.shape
 leading : ∀ t,Jr b t→qQ.aSa M.iF.toNat rows t.shape
 shift : ∀ t,Jr b t→qQ.bk4 M.iF.toNat rows t.shape
 ajB : ∀ t,Jr b t→bbk M.iF.toNat t rows
structure akE (h:ℕ) (rows :vP) (s :Ls) where
 free :Jet
 moving:Jet
 free_ne :free≠0
 moving_ne :moving≠0
 free_mem:free∈rows s.free.shape (anM h s.dI s.free.shape)
 moving_mem:moving∈rows s.moving.shape (anM h s.dI s.moving.shape)
 no_moving:qQ.aeH free moving
abbrev Pairs (b:FarBand) (h:ℕ) (rows :vP) :=
 ∀ s∈b.row.stages,akE h rows s
def agA (rows :vP) (s :Shape) (q:zI) :Prop :=
 ∀ P∈rows s (O2 s),P∈q.asIdeal
def axS {h rows s} (pair :akE h rows s) (q:zI) :Prop :=
  agA rows s.free.shape q∧agA rows s.moving.shape q ∧
    YZ.compatible pair.free pair.moving q
def axy {A u del} (M:jG u del) {Γ} (F:P1.bje A M Γ)
    (q:zI) (γ:K) :Prop :=
  q.asIdeal≤RingHom.ker
    (eval₂RingHom (eval₂RingHom (qD (M.label γ)) (kr (F.scalar γ)))
      (kr (F.scalar γ).derivative))
def Lc (b:FarBand) :Test b→Bank
 | none=>terminal b
 | some i=>dfG b i
def threshold (b:FarBand) :Test b→ℕ
 | none=>b.row.gw.length+1
 | some i=>i.val+1
def apo (b:FarBand) :Test b→ℕ
 | none=>0
 | some i=>(cV b i).seedCap+1
def ahs (h:ℕ) (s :Shape) (W:ℕ) :=1+(O2 s-W)/(2*h)
def ZN (h:ℕ) (s :Shape) (E v :ℕ) :ℕ :=
  ku s fun q j =>
    let g:=(q-j)/E
    let x :=s.m*farAgreement+j - q*(131071-h)
    let c:= fun a=>slots s.U (a*v)
    (∑ a∈Finset.range g,(c a - c (a+1))*(x - 2*h*(j+a))) +
      c g*(x - 2*h*(j+g))
structure bAN (h:ℕ) (t:Bank) (rows :vP) (f :Equation) :Prop where
 ajB:bbk h t rows
 shape : ∀ W,∀ P∈rows t.shape W,qQ.oU P t.shape
 leading:qQ.aSa h rows t.shape
 divides : ∀ W<t.shape.m*farAgreement,∀ P∈rows t.shape W,P≠0 →
  f^(ahs h t.shape W-P.natDegree)∣P.leadingCoeff
abbrev OneSeedEquation :=FX[X][X]
def NativeSeedBound (g:OneSeedEquation) (H :ℕ) :Prop :=
 ∀ l,(g.coeff l).natDegree≤H
def atNative (g:OneSeedEquation) (z :K) (S:K[X]) :FX :=
 g.eval₂ (evalRingHom (jz z)) (kr S)
abbrev gap (D:ℕ) :=farAgreement - D
abbrev normalWidth (D:ℕ) :=blockLength+D - 2*farAgreement
def WitnessOK (D l:ℕ) (x :NativeWitness) :Prop :=
 if l=1 then True else
 let L:=normalWidth D
 let E :=l+x.g
 let M:=x.W+1+x.j*L
 let high:=(x.g+1)*x.c
 0<x.c∧x.j≤x.g∧l*L≤x.W∧E*L<M ∧
 (x.c+1)*(L*E*(E+1)/2+L*x.j*(x.j+1)/2)<high*M ∧
 l*(l-1)*L≤(2*l-2)*x.W∧(2*l-2)*x.W-l*(l-1)*L<p ∧
 (3*l*l-4*l+2)*L≤(6*l-4)*x.W
def numerator (D l:ℕ) (x :NativeWitness) :ℕ :=
  if l=1 then blockLength else
  let pole :=(6*l-4)*x.W-(3*l*l-4*l+2)*normalWidth D
  max ((7+6*l)*gap D + (2*l+1)*blockLength+pole)
    ((l*(x.c+1)+l+x.g)*gap D)
def NativeGuard (D e rate :ℕ) :Prop :=
 k≤D ∧D <farAgreement∧farAgreement<blockLength∧0< normalWidth D ∧
 0<e∧e<p∧gap D ≤ rate ∧
 ∀ l,1≤l→l≤e → ∃ x,WitnessOK D l x∧numerator D l x≤ rate
def nativeFee (D e H rate :ℕ) :ℕ :=
 if H=0 then e else e+1+(rate*H+gap D - 1)/gap D
end
end P5_7
