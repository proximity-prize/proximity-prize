import ProximityPrize.SubmissionLower.GoldBranch7

set_option Elab.async false
set_option autoImplicit true
set_option maxRecDepth 18000

namespace HighCore82209

abbrev agreement : ℕ := 179935
abbrev heightCap : ℕ := 33345
abbrev Bank := P1_7.Bank
abbrev Stage := P1_7.Stage
abbrev Grade := P1_7.Grade
abbrev debit := P1_7.debit

inductive Band where
  | h2367 | h2395 | h7773
  deriving DecidableEq

open K1_14 (Shape shapeSum triangle slots)
def start : Band → ℕ
  | .h2367 => 2356
  | .h2395 => 2395
  | .h7773 => 7773
def finish : Band → ℕ
  | .h2367 => 2394
  | .h2395 => 7772
  | .h7773 => 33345
def terminal : Band → Bank
  | .h2367 => ⟨⟨6825,9490,2013,250000⟩,0x21575027980000,0xc712452a9ff2⟩
  | .h2395 => ⟨⟨7550,10506,2218,239942⟩,0x2cfea55aa80000,0x129e297a45c0c⟩
  | .h7773 => ⟨⟨124,173,32,1077⟩,0xc4fd80000,0x15c66e5⟩
def grades : Band → List Grade
  | .h2367 => []
  | .h2395 => [⟨357,183418⟩, ⟨352,182486⟩, ⟨347,181095⟩, ⟨341,185101⟩, ⟨335,187654⟩, ⟨329,187748⟩, ⟨322,193653⟩, ⟨315,195395⟩, ⟨307,203011⟩, ⟨299,201548⟩, ⟨289,210336⟩, ⟨276,237758⟩, ⟨261,238373⟩, ⟨244,237823⟩, ⟨224,239141⟩, ⟨202,239235⟩, ⟨178,238897⟩, ⟨151,239330⟩, ⟨122,239402⟩, ⟨90,239942⟩, ⟨57,239668⟩, ⟨21,239868⟩]
  | .h7773 => [⟨25,799⟩, ⟨24,754⟩, ⟨21,910⟩, ⟨17,1044⟩, ⟨11,1049⟩, ⟨2,1077⟩]
def stages : Band → List Stage
  | .h2367 => [⟨0,⟨⟨73,101,22,904⟩,0x2e5640000,0x2f6f2a⟩,⟨⟨349,485,102,14256⟩,0x125f7fc0000,0x59e3ed8b⟩⟩,
    ⟨1,⟨⟨80,111,24,997⟩,0x3c7300000,0x4451ef⟩,⟨⟨358,498,104,17308⟩,0x13bbdc40000,0x6355595b⟩⟩,
    ⟨2,⟨⟨89,123,27,1032⟩,0x536d00000,0x67700d⟩,⟨⟨406,565,119,17594⟩,0x1ceebd00000,0xa5555e6d⟩⟩,
    ⟨3,⟨⟨97,134,30,1092⟩,0x6d1340000,0x931387⟩,⟨⟨425,591,125,19998⟩,0x2141d180000,0xc672a1cc⟩⟩,
    ⟨4,⟨⟨106,147,32,1146⟩,0x8b45c0000,0xcf7010⟩,⟨⟨461,640,135,21289⟩,0x2a445e00000,0x1100a07c3⟩⟩,
    ⟨5,⟨⟨115,159,35,1193⟩,0xb24d00000,0x11d1f9e⟩,⟨⟨515,716,150,21439⟩,0x3a9f1980000,0x1a74a03e8⟩⟩,
    ⟨6,⟨⟨115,160,34,1489⟩,0xae8580000,0x11c9279⟩,⟨⟨579,806,170,21495⟩,0x53ba8f80000,0x2aa645c9f⟩⟩,
    ⟨10,⟨⟨142,197,43,1802⟩,0x14bde80000,0x294fec6⟩,⟨⟨679,944,199,28558⟩,0x86af1a00000,0x5018948c9⟩⟩,
    ⟨16,⟨⟨169,235,50,3212⟩,0x222f040000,0x517adc3⟩,⟨⟨888,1233,260,36703⟩,0x12c890e80000,0xe8ae039a1⟩⟩,
    ⟨14,⟨⟨214,296,66,1590⟩,0x472de80000,0xd30a80f⟩,⟨⟨809,1126,236,34511⟩,0xe2bba140000,0xa12bddaf7⟩⟩,
    ⟨24,⟨⟨216,299,66,4213⟩,0x48ac040000,0xd9f9f46⟩,⟨⟨1185,1646,346,46682⟩,0x2c7b45940000,0x2dfe19c180⟩⟩,
    ⟨32,⟨⟨261,362,81,5566⟩,0x813b280000,0x1d6fb003⟩,⟨⟨1450,2015,424,57915⟩,0x5186864c0000,0x6746edbc88⟩⟩,
    ⟨35,⟨⟨259,359,81,11043⟩,0x7f07680000,0x1ca909eb⟩,⟨⟨1274,1771,373,94440⟩,0x375ff1cc0000,0x3db5501b19⟩⟩,
    ⟨51,⟨⟨429,593,135,5201⟩,0x23fdde00000,0xd4e9369b⟩,⟨⟨2025,2816,590,88212⟩,0xdd3ba2e40000,0x1882537ea3b⟩⟩,
    ⟨76,⟨⟨611,846,188,7151⟩,0x65e80780000,0x35e195e5b⟩,⟨⟨2993,4162,879,116184⟩,0x2ce2150400000,0x75919b3c614⟩⟩,
    ⟨103,⟨⟨776,1076,242,9954⟩,0xd28dc840000,0x8e03abac2⟩,⟨⟨4126,5736,1211,146069⟩,0x757a25a480000,0x1a7cbea93549⟩⟩,
    ⟨154,⟨⟨1162,1609,361,13454⟩,0x2bf86f440000,0x2c2f29a34d⟩,⟨⟨6051,8413,1776,210016⟩,0x172699d8580000,0x7a821d9dae58⟩⟩]
  | .h2395 => [⟨0,⟨⟨73,101,22,806⟩,0x2e5640000,0x2f6f2a⟩,⟨⟨352,489,103,11122⟩,0x12dda700000,0x5cfd94a5⟩⟩,
    ⟨1,⟨⟨78,108,24,925⟩,0x392740000,0x3e9e8f⟩,⟨⟨345,480,101,13592⟩,0x11c61f80000,0x564a51c0⟩⟩,
    ⟨2,⟨⟨86,119,26,990⟩,0x4b3780000,0x5a8245⟩,⟨⟨385,535,112,14451⟩,0x188bf840000,0x84679137⟩⟩,
    ⟨3,⟨⟨94,130,29,1043⟩,0x633bc0000,0x822d2c⟩,⟨⟨411,572,120,15860⟩,0x1dec1a80000,0xad1e0c80⟩⟩,
    ⟨4,⟨⟨102,141,31,1111⟩,0x7cec00000,0xb15384⟩,⟨⟨438,609,128,17279⟩,0x2436d340000,0xde912dc3⟩⟩,
    ⟨5,⟨⟨108,150,33,1204⟩,0x948040000,0xe271e9⟩,⟨⟨522,726,153,16683⟩,0x3d548e40000,0x1c16ef1c7⟩⟩,
    ⟨6,⟨⟨108,149,33,1502⟩,0x948040000,0xdda994⟩,⟨⟨570,792,167,17531⟩,0x4fc3e700000,0x27c2e15db⟩⟩,
    ⟨10,⟨⟨142,197,43,1638⟩,0x14bde80000,0x294fec6⟩,⟨⟨696,968,204,22160⟩,0x910a3980000,0x5884788a7⟩⟩,
    ⟨16,⟨⟨163,226,50,2999⟩,0x1f8a780000,0x47e88b5⟩,⟨⟨851,1183,249,30224⟩,0x108708880000,0xc4f2a7606⟩⟩,
    ⟨18,⟨⟨221,306,68,1917⟩,0x4e346c0000,0xf032b8c⟩,⟨⟨952,1324,279,31437⟩,0x17270e900000,0x1350bb1fb5⟩⟩,
    ⟨24,⟨⟨212,294,65,3954⟩,0x44e9c40000,0xcc1a54f⟩,⟨⟨1115,1550,329,39324⟩,0x255cff880000,0x2473d5ffe4⟩⟩,
    ⟨32,⟨⟨261,362,82,4833⟩,0x826c0c0000,0x1db6eefa⟩,⟨⟨1463,2034,430,46182⟩,0x54106e900000,0x6b9d823520⟩⟩,
    ⟨36,⟨⟨246,341,75,49539⟩,0x6ae4280000,0x16e7d3b2⟩,⟨⟨1220,1696,357,79898⟩,0x309db61c0000,0x33e3754396⟩⟩,
    ⟨42,⟨⟨279,386,85,49424⟩,0x9b80980000,0x25892b87⟩,⟨⟨1240,1725,359,169975⟩,0x32a0cb700000,0x370899d961⟩⟩,
    ⟨54,⟨⟨534,740,167,4076⟩,0x44f1df00000,0x1ff6e1863⟩,⟨⟨2252,3131,661,69795⟩,0x131ef423c0000,0x25ab1ba8825⟩⟩,
    ⟨81,⟨⟨637,883,197,7195⟩,0x73e2ad80000,0x401d0f0c6⟩,⟨⟨3474,4830,1019,95585⟩,0x461aa92080000,0xd5013df2ef9⟩⟩,
    ⟨100,⟨⟨774,1072,239,8609⟩,0xcf60ca00000,0x8af950b98⟩,⟨⟨4170,5798,1223,115759⟩,0x7934721300000,0x1ba1a89b2ba1⟩⟩,
    ⟨135,⟨⟨1042,1443,329,10800⟩,0x201c60040000,0x1cf53a5560⟩,⟨⟨5487,7630,1607,152713⟩,0x113c22e7a00000,0x52bdbe618ec3⟩⟩]
  | .h7773 => [⟨0,⟨⟨11,15,3,126⟩,0x3500000,0x892⟩,⟨⟨20,28,4,259⟩,0xdc00000,0x4287⟩⟩,
    ⟨2,⟨⟨21,29,6,152⟩,0x13cc0000,0x609d⟩,⟨⟨38,53,9,379⟩,0x5d840000,0x33bc5⟩⟩,
    ⟨5,⟨⟨34,47,10,231⟩,0x4f100000,0x26533⟩,⟨⟨64,89,15,593⟩,0x1a3600000,0x17e10a⟩⟩,
    ⟨10,⟨⟨54,75,16,381⟩,0x12f140000,0xe9a95⟩,⟨⟨101,141,24,995⟩,0x64f3c0000,0x91e8ba⟩⟩]
def fees : Band → P1_7.PrefixFees
  | .h2367 => ⟨0x104eb1adae16a86,0x1dfc76b97e,0x32e9cf232eeb3,0x5ae3244351ebaa,0x14262d7100e9,0x1d60c8007670⟩
  | .h2395 => ⟨0xc1c3fd05f5589a,0x19585647de,0x2ca647728e1b6,0x48a20cd7e1cd93,0x14c3ba803e8e,0x171d68005d30⟩
  | .h7773 => ⟨0x26bd932c5bdcf,0xf9e0df,0xe5d8b00f768,0x78ee8dbb183,0x16ddfe0aa,0xbeff000302⟩
def retainedCap : Band → ℕ
  | .h2367 => 0x2513fe86c08f43a
  | .h2395 => 0x280388b8e5114e7
  | .h7773 => 0x122aedc9e205a
def highBound : Band → ℕ
  | .h2367 => 0x3b46e696e5769f5
  | .h2395 => 0x38d94f45e280067
  | .h7773 => 0x3a534f11a4ba0

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

theorem height_cover {h : ℕ} (lo : 2356 ≤ h) (hi : h ≤ heightCap) :
    ∃ b, start b ≤ h ∧ h ≤ finish b := by
  by_cases h0 : h ≤ 2394
  · exact ⟨.h2367, lo, h0⟩
  by_cases h1 : h ≤ 7772
  · exact ⟨.h2395, by change 2395 ≤ h; omega, h1⟩
  exact ⟨.h7773, by change 7773 ≤ h; omega, hi⟩

theorem accounting (b : Band) :
    (fees b).loss + (fees b).point + (fees b).lowSeed + (fees b).lowJet +
       (fees b).fixedODE + (fees b).content + retainedCap b + 1 = highBound b ∧
       highBound b ≤ 266959677023545845 := by
  cases b <;> decide +kernel

end HighCore82209
