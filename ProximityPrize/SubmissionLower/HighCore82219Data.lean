import ProximityPrize.SubmissionLower.GoldBranch7

set_option autoImplicit true
set_option maxRecDepth 18000

namespace HighCore82219

abbrev agreement : ℕ := 179895
abbrev heightCap : ℕ := 33425
abbrev Bank := P1_7.Bank
abbrev Stage := P1_7.Stage
abbrev Grade := P1_7.Grade
abbrev debit := P1_7.debit

inductive Band where
  | h2367 | h2395 | h7773
  deriving DecidableEq

open K1_14 (Shape shapeSum triangle slots)
def start : Band → ℕ
  | .h2367 => 2391
  | .h2395 => 2491
  | .h7773 => 7880
def finish : Band → ℕ
  | .h2367 => 2490
  | .h2395 => 7879
  | .h7773 => 33425
def terminal : Band → Bank
  | .h2367 => ⟨⟨4322,6010,1275,375000⟩,0x878be47080000,0x200a9f6cd5af⟩
  | .h2395 => ⟨⟨7550,10506,2218,225000⟩,0x2cfea55aa80000,0x129e297a45c0c⟩
  | .h7773 => ⟨⟨124,173,32,900⟩,0xc4fd80000,0x15c66e5⟩
def grades : Band → List Grade
  | .h2367 => []
  | .h2395 => [⟨365,181533⟩, ⟨360,181341⟩, ⟨354,186683⟩, ⟨349,183485⟩, ⟨343,185397⟩, ⟨336,192822⟩, ⟨330,189998⟩, ⟨322,201376⟩, ⟨315,197135⟩, ⟨306,205550⟩, ⟨296,215543⟩, ⟨285,218969⟩, ⟨272,222566⟩, ⟨257,224442⟩, ⟨241,223407⟩, ⟨222,224228⟩, ⟨201,224635⟩, ⟨178,224832⟩, ⟨153,224928⟩, ⟨126,224982⟩, ⟨98,224490⟩, ⟨67,224613⟩, ⟨34,224744⟩]
  | .h7773 => [⟨26,745⟩, ⟨24,796⟩, ⟨22,822⟩, ⟨19,877⟩, ⟨15,885⟩, ⟨9,899⟩, ⟨2,894⟩]
def stages : Band → List Stage
  | .h2367 => [⟨0,⟨⟨76,105,23,901⟩,0x345100000,0x3777f9⟩,⟨⟨437,608,128,16810⟩,0x2407b5c0000,0xdd657d32⟩⟩,
    ⟨1,⟨⟨83,115,25,998⟩,0x439080000,0x4ed4ac⟩,⟨⟨436,606,128,20066⟩,0x23d8b880000,0xdb115372⟩⟩,
    ⟨2,⟨⟨92,127,28,1053⟩,0x5c3600000,0x75b415⟩,⟨⟨508,706,149,20548⟩,0x389233c0000,0x19280bd7d⟩⟩,
    ⟨3,⟨⟨99,137,30,1145⟩,0x722180000,0x9dd5af⟩,⟨⟨493,686,144,24971⟩,0x338ed2c0000,0x1656b0db4⟩⟩,
    ⟨4,⟨⟨107,148,33,1211⟩,0x917680000,0xd8f2fa⟩,⟨⟨526,731,154,27244⟩,0x3eb17680000,0x1cdc7da38⟩⟩,
    ⟨5,⟨⟨116,161,35,1282⟩,0xb5c380000,0x128bb48⟩,⟨⟨641,892,188,25381⟩,0x716c8a40000,0x3fe068fa5⟩⟩,
    ⟨7,⟨⟨126,175,39,1534⟩,0xec9f00000,0x1a458a5⟩,⟨⟨685,952,201,30186⟩,0x8a677880000,0x52f0bdb9b⟩⟩,
    ⟨10,⟨⟨142,197,43,2006⟩,0x14bde80000,0x294fec6⟩,⟨⟨864,1202,254,33443⟩,0x115b81bc0000,0xd28832ce8⟩⟩,
    ⟨16,⟨⟨171,237,50,3788⟩,0x2316e80000,0x53b7f45⟩,⟨⟨1015,1412,298,47394⟩,0x1c16f6f00000,0x1901657cf3⟩⟩,
    ⟨10,⟨⟨178,247,55,1426⟩,0x2932d00000,0x66c8fdf⟩,⟨⟨792,1101,233,36048⟩,0xd623cb40000,0x947787094⟩⟩,
    ⟨20,⟨⟨251,347,78,2220⟩,0x7322680000,0x18f6d6a4⟩,⟨⟨1305,1815,383,49738⟩,0x3b9eea000000,0x442ac5ba92⟩⟩,
    ⟨32,⟨⟨261,362,81,6883⟩,0x813b280000,0x1d6fb003⟩,⟨⟨1463,2035,429,92074⟩,0x53ea2df80000,0x6b96ecc888⟩⟩,
    ⟨31,⟨⟨345,478,108,2979⟩,0x12b1e340000,0x59a98629⟩,⟨⟨1607,2235,472,74026⟩,0x6f51ac300000,0x9cb2a062f8⟩⟩,
    ⟨44,⟨⟨377,522,118,5296⟩,0x185d2840000,0x7f6275d9⟩,⟨⟨2259,3142,664,91496⟩,0x1352184380000,0x263b0eab16b⟩⟩,
    ⟨73,⟨⟨600,831,188,7388⟩,0x61d88780000,0x32de21d13⟩,⟨⟨3496,4863,1027,139651⟩,0x4786bafb80000,0xdb0e8041cee⟩⟩,
    ⟨76,⟨⟨499,692,155,27035⟩,0x38015300000,0x185234383⟩,⟨⟨2767,3850,812,236474⟩,0x2372addc00000,0x5601e71ab3f⟩⟩,
    ⟨103,⟨⟨812,1126,252,10165⟩,0xf04a9400000,0xa99a27482⟩,⟨⟨4786,6667,1405,189419⟩,0xb759a72bc0000,0x304357eb723c⟩⟩]
  | .h2395 => [⟨0,⟨⟨73,101,22,736⟩,0x2e5640000,0x2f6f2a⟩,⟨⟨352,489,103,10741⟩,0x12dda700000,0x5cfd94a5⟩⟩,
    ⟨1,⟨⟨78,108,24,845⟩,0x392740000,0x3e9e8f⟩,⟨⟨345,480,101,12990⟩,0x11c61f80000,0x564a51c0⟩⟩,
    ⟨2,⟨⟨86,119,26,915⟩,0x4b3780000,0x5a8245⟩,⟨⟨385,535,112,13930⟩,0x188bf840000,0x84679137⟩⟩,
    ⟨3,⟨⟨94,130,29,973⟩,0x633bc0000,0x822d2c⟩,⟨⟨411,572,120,15343⟩,0x1dec1a80000,0xad1e0c80⟩⟩,
    ⟨4,⟨⟨102,141,31,1044⟩,0x7cec00000,0xb15384⟩,⟨⟨438,609,128,16783⟩,0x2436d340000,0xde912dc3⟩⟩,
    ⟨5,⟨⟨108,150,33,1134⟩,0x948040000,0xe271e9⟩,⟨⟨522,726,153,16434⟩,0x3d548e40000,0x1c16ef1c7⟩⟩,
    ⟨6,⟨⟨108,149,33,1396⟩,0x948040000,0xdda994⟩,⟨⟨570,792,167,17344⟩,0x4fc3e700000,0x27c2e15db⟩⟩,
    ⟨10,⟨⟨142,197,43,1566⟩,0x14bde80000,0x294fec6⟩,⟨⟨696,968,204,22064⟩,0x910a3980000,0x5884788a7⟩⟩,
    ⟨16,⟨⟨163,226,50,2828⟩,0x1f8a780000,0x47e88b5⟩,⟨⟨851,1183,249,30271⟩,0x108708880000,0xc4f2a7606⟩⟩,
    ⟨18,⟨⟨221,306,68,1882⟩,0x4e346c0000,0xf032b8c⟩,⟨⟨952,1324,279,31580⟩,0x17270e900000,0x1350bb1fb5⟩⟩,
    ⟨24,⟨⟨212,294,65,3793⟩,0x44e9c40000,0xcc1a54f⟩,⟨⟨1115,1550,329,39745⟩,0x255cff880000,0x2473d5ffe4⟩⟩,
    ⟨32,⟨⟨261,362,82,4688⟩,0x826c0c0000,0x1db6eefa⟩,⟨⟨1463,2034,430,46807⟩,0x54106e900000,0x6b9d823520⟩⟩,
    ⟨36,⟨⟨246,341,75,36353⟩,0x6ae4280000,0x16e7d3b2⟩,⟨⟨1220,1696,357,81482⟩,0x309db61c0000,0x33e3754396⟩⟩,
    ⟨42,⟨⟨279,386,85,39379⟩,0x9b80980000,0x25892b87⟩,⟨⟨1240,1725,359,174982⟩,0x32a0cb700000,0x370899d961⟩⟩,
    ⟨54,⟨⟨534,740,167,4069⟩,0x44f1df00000,0x1ff6e1863⟩,⟨⟨2252,3131,661,71080⟩,0x131ef423c0000,0x25ab1ba8825⟩⟩,
    ⟨81,⟨⟨637,883,197,7196⟩,0x73e2ad80000,0x401d0f0c6⟩,⟨⟨3474,4830,1019,97432⟩,0x461aa92080000,0xd5013df2ef9⟩⟩,
    ⟨100,⟨⟨774,1072,239,8631⟩,0xcf60ca00000,0x8af950b98⟩,⟨⟨4170,5798,1223,118124⟩,0x7934721300000,0x1ba1a89b2ba1⟩⟩,
    ⟨135,⟨⟨1042,1443,329,10850⟩,0x201c60040000,0x1cf53a5560⟩,⟨⟨5487,7630,1607,155967⟩,0x113c22e7a00000,0x52bdbe618ec3⟩⟩]
  | .h7773 => [⟨0,⟨⟨11,15,3,122⟩,0x3500000,0x892⟩,⟨⟨20,28,4,256⟩,0xdc00000,0x4287⟩⟩,
    ⟨2,⟨⟨21,29,6,151⟩,0x13cc0000,0x609d⟩,⟨⟨38,53,9,382⟩,0x5d840000,0x33bc5⟩⟩,
    ⟨5,⟨⟨34,47,10,233⟩,0x4f100000,0x26533⟩,⟨⟨64,89,15,601⟩,0x1a3600000,0x17e10a⟩⟩,
    ⟨10,⟨⟨54,75,16,386⟩,0x12f140000,0xe9a95⟩,⟨⟨101,141,24,1014⟩,0x64f3c0000,0x91e8ba⟩⟩]
def fees : Band → P1_7.PrefixFees
  | .h2367 => ⟨0x18fda64a667d171,0x2e03840e3c,0x39f8ec7381c5e,0x1cf1,0xfb0a3e054bf,0x225251008a5e⟩
  | .h2395 => ⟨0xbb3512c8021d8a,0x167d6414f6,0x2a0c067256fed,0x405ad688119ca0,0x14c90208f140,0x163dab0059aa⟩
  | .h7773 => ⟨0x26498941b6f05,0xea00e4,0xe0fa800ecd4,0x741fa0ca161,0x16e2249ab,0xbb860002f4⟩
def retainedCap : Band → ℕ
  | .h2367 => 0x2361953a2e1bfd5
  | .h2395 => 0x2a9c7bba62375a8
  | .h7773 => 0x1228334f28764
def highBound : Band → ℕ
  | .h2367 => 0x3c9c57808e6b7ef
  | .h2395 => 0x3a8238287c9ffa0
  | .h7773 => 0x39d2a6027d222

def subbank (b : Band) (g : Grade) : Bank :=
  let t := terminal b
  { t with shape := { t.shape with U := g.slots } }

abbrev GradeIndex (b : Band) := Fin (grades b).length

def Listed (b : Band) (t : Bank) : Prop :=
  t = terminal b ∨ (∃ s ∈ stages b, t = s.free ∨ t = s.moving) ∨
    ∃ i : GradeIndex b, t = subbank b ((grades b).get i)

abbrev Test (b : Band) := Option (GradeIndex b)

def tested (b : Band) : Test b → Bank
  | none => terminal b
  | some i => subbank b ((grades b).get i)

def threshold (b : Band) : Test b → ℕ
  | none => (grades b).length + 1
  | some i => i.val + 1

def seedThreshold (b : Band) : Test b → ℕ
  | none => 0
  | some i => ((grades b).get i).seedCap + 1

def jointGain (h : ℕ) (s : Shape) (E v : ℕ) : ℕ :=
  shapeSum s fun q j =>
    let g := (q-j)/E
    let x := s.m*agreement+j - q*(131071-h)
    let c := fun a => slots s.U (a*v)
    (∑ a ∈ Finset.range g, (c a - c (a+1)) * (x - 2*h*(j+a))) +
      c g * (x - 2*h*(j+g))

def cutoffCount (h r : ℕ) (s : Shape) : ℕ :=
  s.m * agreement - 2 * h * r

def rawWidth (h r : ℕ) (s : Shape) (q j : ℕ) : ℕ :=
  cutoffCount h r s + j - q * (131071 - h)

def WidthGuard (h r : ℕ) (s : Shape) : Prop :=
  s.B * (131071-h) < cutoffCount h r s

def gain (h r : ℕ) (s : Shape) (mode : ℕ) : ℕ :=
  triangle s.U * shapeSum s (fun q j => rawWidth h r s q j - mode * (2 * h * j))

theorem height_cover {h : ℕ} (lo : 2391 ≤ h) (hi : h ≤ heightCap) :
    ∃ b, start b ≤ h ∧ h ≤ finish b := by
  by_cases h0 : h ≤ 2490
  · exact ⟨.h2367, lo, h0⟩
  by_cases h1 : h ≤ 7879
  · exact ⟨.h2395, by change 2491 ≤ h; omega, h1⟩
  exact ⟨.h7773, by change 7880 ≤ h; omega, hi⟩

theorem accounting (b : Band) :
    (fees b).loss + (fees b).point + (fees b).lowSeed + (fees b).lowJet +
       (fees b).fixedODE + (fees b).content + retainedCap b + 1 = highBound b ∧
       highBound b ≤ 272966371768711151 := by
  cases b <;> decide +kernel

end HighCore82219
