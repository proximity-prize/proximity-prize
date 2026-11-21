import ProximityPrize.SubmissionLower.GoldBranch7

set_option Elab.async false
set_option autoImplicit true
set_option maxRecDepth 18000

namespace HighCore82229

abbrev agreement : ℕ := 179915
abbrev heightCap : ℕ := 33385
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
  | .h2395 => 2440
  | .h7773 => 7773
def finish : Band → ℕ
  | .h2367 => 2439
  | .h2395 => 7772
  | .h7773 => 33385
def terminal : Band → Bank
  | .h2367 => ⟨⟨4625,6431,1364,373000⟩,0xa60d3e1440000,0x29ff0aaee26a⟩
  | .h2395 => ⟨⟨7550,10506,2218,225000⟩,0x2cfea55aa80000,0x129e297a45c0c⟩
  | .h7773 => ⟨⟨124,173,32,900⟩,0xc4fd80000,0x15c66e5⟩
def grades : Band → List Grade
  | .h2367 => []
  | .h2395 => [⟨365,181533⟩, ⟨360,181341⟩, ⟨354,186683⟩, ⟨349,183485⟩, ⟨343,185397⟩, ⟨336,192822⟩, ⟨330,189998⟩, ⟨322,201376⟩, ⟨315,197135⟩, ⟨306,205550⟩, ⟨296,215543⟩, ⟨285,218969⟩, ⟨272,222566⟩, ⟨257,224442⟩, ⟨241,223407⟩, ⟨222,224228⟩, ⟨201,224635⟩, ⟨178,224832⟩, ⟨153,224928⟩, ⟨126,224982⟩, ⟨98,224490⟩, ⟨67,224613⟩, ⟨34,224744⟩]
  | .h7773 => [⟨26,745⟩, ⟨24,796⟩, ⟨22,822⟩, ⟨19,877⟩, ⟨15,885⟩, ⟨9,899⟩, ⟨2,894⟩]
def stages : Band → List Stage
  | .h2367 => [⟨0,⟨⟨76,105,23,915⟩,0x345100000,0x3777f9⟩,⟨⟨437,608,128,15861⟩,0x2407b5c0000,0xdd657d32⟩⟩,
    ⟨1,⟨⟨83,115,25,1010⟩,0x439080000,0x4ed4ac⟩,⟨⟨436,606,128,18714⟩,0x23d8b880000,0xdb115372⟩⟩,
    ⟨2,⟨⟨92,127,28,1062⟩,0x5c3600000,0x75b415⟩,⟨⟨508,706,149,19257⟩,0x389233c0000,0x19280bd7d⟩⟩,
    ⟨3,⟨⟨99,137,30,1152⟩,0x722180000,0x9dd5af⟩,⟨⟨492,686,144,23186⟩,0x33533580000,0x1656b0db4⟩⟩,
    ⟨4,⟨⟨107,148,33,1215⟩,0x917680000,0xd8f2fa⟩,⟨⟨525,731,154,25099⟩,0x3e6d7fc0000,0x1cdc7da38⟩⟩,
    ⟨5,⟨⟨116,161,35,1284⟩,0xb5c380000,0x128bb48⟩,⟨⟨642,892,188,23738⟩,0x71d1af40000,0x3fe068fa5⟩⟩,
    ⟨7,⟨⟨126,175,39,1533⟩,0xec9f00000,0x1a458a5⟩,⟨⟨685,952,201,27968⟩,0x8a677880000,0x52f0bdb9b⟩⟩,
    ⟨10,⟨⟨142,197,43,1997⟩,0x14bde80000,0x294fec6⟩,⟨⟨865,1202,254,31183⟩,0x1166fe340000,0xd28832ce8⟩⟩,
    ⟨16,⟨⟨171,237,50,3738⟩,0x2316e80000,0x53b7f45⟩,⟨⟨1014,1412,298,43547⟩,0x1c0729180000,0x1901657cf3⟩⟩,
    ⟨10,⟨⟨178,247,55,1418⟩,0x2932d00000,0x66c8fdf⟩,⟨⟨792,1101,233,33236⟩,0xd623cb40000,0x947787094⟩⟩,
    ⟨20,⟨⟨250,347,78,2198⟩,0x721cb80000,0x18f6d6a4⟩,⟨⟨1302,1815,383,46412⟩,0x3b50b1000000,0x442ac5ba92⟩⟩,
    ⟨32,⟨⟨261,362,81,6668⟩,0x813b280000,0x1d6fb003⟩,⟨⟨1459,2035,429,82316⟩,0x536744d80000,0x6b96ecc888⟩⟩,
    ⟨31,⟨⟨345,478,108,2941⟩,0x12b1e340000,0x59a98629⟩,⟨⟨1604,2235,472,67896⟩,0x6edb04b80000,0x9cb2a062f8⟩⟩,
    ⟨44,⟨⟨376,522,118,5200⟩,0x183833c0000,0x7f6275d9⟩,⟨⟨2253,3142,664,84839⟩,0x1334cd7ac0000,0x263b0eab16b⟩⟩,
    ⟨73,⟨⟨599,831,188,7234⟩,0x617b2300000,0x32de21d13⟩,⟨⟨3486,4863,1027,129506⟩,0x4711f2a780000,0xdb0e8041cee⟩⟩,
    ⟨76,⟨⟨498,692,155,25080⟩,0x37c11c80000,0x185234383⟩,⟨⟨2760,3850,812,202285⟩,0x233f7cff80000,0x5601e71ab3f⟩⟩,
    ⟨103,⟨⟨809,1126,252,10013⟩,0xee4ed940000,0xa99a27482⟩,⟨⟨4774,6667,1405,176011⟩,0xb6532fbfc0000,0x304357eb723c⟩⟩]
  | .h2395 => [⟨0,⟨⟨73,101,22,775⟩,0x2e5640000,0x2f6f2a⟩,⟨⟨352,489,103,11096⟩,0x12dda700000,0x5cfd94a5⟩⟩,
    ⟨1,⟨⟨78,108,24,890⟩,0x392740000,0x3e9e8f⟩,⟨⟨345,480,101,13538⟩,0x11c61f80000,0x564a51c0⟩⟩,
    ⟨2,⟨⟨86,119,26,958⟩,0x4b3780000,0x5a8245⟩,⟨⟨385,535,112,14444⟩,0x188bf840000,0x84679137⟩⟩,
    ⟨3,⟨⟨94,130,29,1013⟩,0x633bc0000,0x822d2c⟩,⟨⟨411,572,120,15887⟩,0x1dec1a80000,0xad1e0c80⟩⟩,
    ⟨4,⟨⟨102,141,31,1083⟩,0x7cec00000,0xb15384⟩,⟨⟨438,609,128,17350⟩,0x2436d340000,0xde912dc3⟩⟩,
    ⟨5,⟨⟨108,150,33,1175⟩,0x948040000,0xe271e9⟩,⟨⟨522,726,153,16811⟩,0x3d548e40000,0x1c16ef1c7⟩⟩,
    ⟨6,⟨⟨108,149,33,1458⟩,0x948040000,0xdda994⟩,⟨⟨570,792,167,17692⟩,0x4fc3e700000,0x27c2e15db⟩⟩,
    ⟨10,⟨⟨142,197,43,1611⟩,0x14bde80000,0x294fec6⟩,⟨⟨696,968,204,22445⟩,0x910a3980000,0x5884788a7⟩⟩,
    ⟨16,⟨⟨163,226,50,2939⟩,0x1f8a780000,0x47e88b5⟩,⟨⟨851,1183,249,30754⟩,0x108708880000,0xc4f2a7606⟩⟩,
    ⟨18,⟨⟨221,306,68,1908⟩,0x4e346c0000,0xf032b8c⟩,⟨⟨952,1324,279,31997⟩,0x17270e900000,0x1350bb1fb5⟩⟩,
    ⟨24,⟨⟨212,294,65,3909⟩,0x44e9c40000,0xcc1a54f⟩,⟨⟨1115,1550,329,40187⟩,0x255cff880000,0x2473d5ffe4⟩⟩,
    ⟨32,⟨⟨261,362,82,4804⟩,0x826c0c0000,0x1db6eefa⟩,⟨⟨1463,2034,430,47176⟩,0x54106e900000,0x6b9d823520⟩⟩,
    ⟨36,⟨⟨246,341,75,45887⟩,0x6ae4280000,0x16e7d3b2⟩,⟨⟨1220,1696,357,83206⟩,0x309db61c0000,0x33e3754396⟩⟩,
    ⟨42,⟨⟨279,386,85,47570⟩,0x9b80980000,0x25892b87⟩,⟨⟨1240,1725,359,184205⟩,0x32a0cb700000,0x370899d961⟩⟩,
    ⟨54,⟨⟨534,740,167,4088⟩,0x44f1df00000,0x1ff6e1863⟩,⟨⟨2252,3131,661,71443⟩,0x131ef423c0000,0x25ab1ba8825⟩⟩,
    ⟨81,⟨⟨637,883,197,7234⟩,0x73e2ad80000,0x401d0f0c6⟩,⟨⟨3474,4830,1019,97723⟩,0x461aa92080000,0xd5013df2ef9⟩⟩,
    ⟨100,⟨⟨774,1072,239,8665⟩,0xcf60ca00000,0x8af950b98⟩,⟨⟨4170,5798,1223,118424⟩,0x7934721300000,0x1ba1a89b2ba1⟩⟩,
    ⟨135,⟨⟨1042,1443,329,10877⟩,0x201c60040000,0x1cf53a5560⟩,⟨⟨5487,7630,1607,156297⟩,0x113c22e7a00000,0x52bdbe618ec3⟩⟩]
  | .h7773 => [⟨0,⟨⟨11,15,3,129⟩,0x3500000,0x892⟩,⟨⟨20,28,4,266⟩,0xdc00000,0x4287⟩⟩,
    ⟨2,⟨⟨21,29,6,154⟩,0x13cc0000,0x609d⟩,⟨⟨38,53,9,388⟩,0x5d840000,0x33bc5⟩⟩,
    ⟨5,⟨⟨34,47,10,235⟩,0x4f100000,0x26533⟩,⟨⟨64,89,15,605⟩,0x1a3600000,0x17e10a⟩⟩,
    ⟨10,⟨⟨54,75,16,387⟩,0x12f140000,0xe9a95⟩,⟨⟨101,141,24,1017⟩,0x64f3c0000,0x91e8ba⟩⟩]
def fees : Band → P1_7.PrefixFees
  | .h2367 => ⟨0x17658ae07d74b28,0x2ce9681190,0x38f461a3662ec,0x705f76165d5412,0xfaea8fab5fb,0x208278008310⟩
  | .h2395 => ⟨0xbede600bacefbe,0x17821ebf6a,0x2bb83f427b2d9,0x4592308a0416ae,0x14c451c63b7d,0x170121005cbe⟩
  | .h7773 => ⟨0x272ecfcc4ced9,0xfc7a91,0xebb4e01026f,0x7f40ad418b6,0x16e011438,0xc3f5000316⟩
def retainedCap : Band → ℕ
  | .h2367 => 0x1cdad53325bf050
  | .h2395 => 0x2aa3d29227465de
  | .h7773 => 0x122d73cbf60cd
def highBound : Band → ℕ
  | .h2367 => 0x3b8251b752a3d12
  | .h2395 => 0x3b1951aa13276c9
  | .h7773 => 0x3ad38f656dcab

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
  by_cases h0 : h ≤ 2439
  · exact ⟨.h2367, lo, h0⟩
  by_cases h1 : h ≤ 7772
  · exact ⟨.h2395, by change 2440 ≤ h; omega, h1⟩
  exact ⟨.h7773, by change 7773 ≤ h; omega, hi⟩

theorem accounting (b : Band) :
    (fees b).loss + (fees b).point + (fees b).lowSeed + (fees b).lowJet +
       (fees b).fixedODE + (fees b).content + retainedCap b + 1 = highBound b ∧
       highBound b ≤ 268265986140156442 := by
  cases b <;> decide +kernel

end HighCore82229
