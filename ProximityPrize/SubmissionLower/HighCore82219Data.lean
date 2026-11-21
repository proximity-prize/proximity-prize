import ProximityPrize.SubmissionLower.GoldBranch7

set_option Elab.async false
set_option autoImplicit true
set_option maxRecDepth 18000

namespace HighCore82219

abbrev agreement : ℕ := 179925
abbrev heightCap : ℕ := 33365
abbrev Bank := P1_7.Bank
abbrev Stage := P1_7.Stage
abbrev Grade := P1_7.Grade
abbrev debit := P1_7.debit

inductive Band where
  | h2367 | h2395 | h7773
  deriving DecidableEq

open K1_14 (Shape shapeSum triangle slots)
def start : Band → ℕ
  | .h2367 => 2342
  | .h2395 => 2415
  | .h7773 => 7773
def finish : Band → ℕ
  | .h2367 => 2414
  | .h2395 => 7772
  | .h7773 => 33365
def terminal : Band → Bank
  | .h2367 => ⟨⟨6825,9490,2013,240000⟩,0x21575027980000,0xc712452a9ff2⟩
  | .h2395 => ⟨⟨7550,10506,2218,229924⟩,0x2cfea55aa80000,0x129e297a45c0c⟩
  | .h7773 => ⟨⟨124,173,32,949⟩,0xc4fd80000,0x15c66e5⟩
def grades : Band → List Grade
  | .h2367 => []
  | .h2395 => [⟨365,179010⟩, ⟨359,185266⟩, ⟨354,183202⟩, ⟨348,186942⟩, ⟨342,189067⟩, ⟨336,188960⟩, ⟨329,194045⟩, ⟨322,195714⟩, ⟨314,201989⟩, ⟨306,201870⟩, ⟨296,210653⟩, ⟨284,223669⟩, ⟨270,229924⟩, ⟨255,228680⟩, ⟨238,228103⟩, ⟨218,229092⟩, ⟨196,229493⟩, ⟨172,229615⟩, ⟨146,229607⟩, ⟨118,229548⟩, ⟨88,229477⟩, ⟨55,229895⟩, ⟨21,229805⟩]
  | .h7773 => [⟨26,729⟩, ⟨24,773⟩, ⟨22,800⟩, ⟨18,949⟩, ⟨14,916⟩, ⟨7,943⟩]
def stages : Band → List Stage
  | .h2367 => [⟨0,⟨⟨76,105,23,912⟩,0x345100000,0x3777f9⟩,⟨⟨402,560,118,15956⟩,0x1c1ecd80000,0x9fa2a66a⟩⟩,
    ⟨1,⟨⟨83,115,25,1006⟩,0x439080000,0x4ed4ac⟩,⟨⟨400,556,117,19545⟩,0x1ba15fc0000,0x9afa738a⟩⟩,
    ⟨2,⟨⟨92,127,28,1056⟩,0x5c3600000,0x75b415⟩,⟨⟨460,640,135,19784⟩,0x2a101b00000,0x1100a07c3⟩⟩,
    ⟨3,⟨⟨99,137,30,1144⟩,0x722180000,0x9dd5af⟩,⟨⟨500,695,146,21314⟩,0x35c3f9c0000,0x178b58789⟩⟩,
    ⟨4,⟨⟨106,147,32,1240⟩,0x8b45c0000,0xcf7010⟩,⟨⟨576,803,168,21671⟩,0x52059700000,0x29c15d15d⟩⟩,
    ⟨5,⟨⟨116,161,35,1273⟩,0xb5c380000,0x128bb48⟩,⟨⟨570,792,167,24708⟩,0x4fc3e700000,0x27c2e15db⟩⟩,
    ⟨6,⟨⟨114,158,34,1636⟩,0xab2c00000,0x11160fc⟩,⟨⟨649,905,191,24813⟩,0x76055000000,0x43bec1daa⟩⟩,
    ⟨10,⟨⟨142,197,43,1972⟩,0x14bde80000,0x294fec6⟩,⟨⟨770,1070,226,32074⟩,0xc4787600000,0x84449c619⟩⟩,
    ⟨16,⟨⟨171,237,50,3656⟩,0x2316e80000,0x53b7f45⟩,⟨⟨977,1363,286,42629⟩,0x18fff4d40000,0x159e2d5716⟩⟩,
    ⟨14,⟨⟨198,275,61,1785⟩,0x386e7c0000,0x9cf007b⟩,⟨⟨977,1364,286,36820⟩,0x18fff4d40000,0x15ab3b8fbf⟩⟩,
    ⟨24,⟨⟨280,389,86,2499⟩,0x9e21bc0000,0x26d3f271⟩,⟨⟨1425,1989,418,50764⟩,0x4d9248740000,0x61f51befe2⟩⟩,
    ⟨32,⟨⟨261,362,81,6457⟩,0x813b280000,0x1d6fb003⟩,⟨⟨1520,2112,447,70888⟩,0x5e4e46800000,0x7d30624510⟩⟩,
    ⟨35,⟨⟨259,359,80,15517⟩,0x7dda980000,0x1c63733f⟩,⟨⟨1303,1818,382,146812⟩,0x3b4c65500000,0x4463d9bf23⟩⟩,
    ⟨42,⟨⟨367,510,115,4761⟩,0x1680b100000,0x73e3968f⟩,⟨⟨1912,2669,560,86234⟩,0xbaffc5900000,0x13cdc61e0d1⟩⟩,
    ⟨51,⟨⟨443,616,139,5216⟩,0x27880f00000,0xf61a28de⟩,⟨⟨2454,3427,717,93122⟩,0x18a691f5c0000,0x35abaf976d5⟩⟩,
    ⟨76,⟨⟨608,846,188,7770⟩,0x64ca5080000,0x35e195e5b⟩,⟨⟨3678,5137,1083,125904⟩,0x536ebb3480000,0x1105d97d500b⟩⟩,
    ⟨103,⟨⟨809,1126,252,9823⟩,0xee4ed940000,0xa99a27482⟩,⟨⟨4774,6667,1405,166048⟩,0xb6532fbfc0000,0x304357eb723c⟩⟩,
    ⟨154,⟨⟨1201,1672,376,13534⟩,0x30d331640000,0x339a80c8e3⟩,⟨⟨6672,9318,1962,245740⟩,0x1f13f8d6640000,0xb7f7289fe1d3⟩⟩]
  | .h2395 => [⟨0,⟨⟨73,101,22,795⟩,0x2e5640000,0x2f6f2a⟩,⟨⟨352,489,103,11258⟩,0x12dda700000,0x5cfd94a5⟩⟩,
    ⟨1,⟨⟨78,108,24,913⟩,0x392740000,0x3e9e8f⟩,⟨⟨345,480,101,13793⟩,0x11c61f80000,0x564a51c0⟩⟩,
    ⟨2,⟨⟨86,119,26,980⟩,0x4b3780000,0x5a8245⟩,⟨⟨385,535,112,14677⟩,0x188bf840000,0x84679137⟩⟩,
    ⟨3,⟨⟨94,130,29,1034⟩,0x633bc0000,0x822d2c⟩,⟨⟨411,572,120,16131⟩,0x1dec1a80000,0xad1e0c80⟩⟩,
    ⟨4,⟨⟨102,141,31,1103⟩,0x7cec00000,0xb15384⟩,⟨⟨438,609,128,17600⟩,0x2436d340000,0xde912dc3⟩⟩,
    ⟨5,⟨⟨108,150,33,1196⟩,0x948040000,0xe271e9⟩,⟨⟨522,726,153,16967⟩,0x3d548e40000,0x1c16ef1c7⟩⟩,
    ⟨6,⟨⟨108,149,33,1491⟩,0x948040000,0xdda994⟩,⟨⟨570,792,167,17833⟩,0x4fc3e700000,0x27c2e15db⟩⟩,
    ⟨10,⟨⟨142,197,43,1633⟩,0x14bde80000,0x294fec6⟩,⟨⟨696,968,204,22588⟩,0x910a3980000,0x5884788a7⟩⟩,
    ⟨16,⟨⟨163,226,50,2995⟩,0x1f8a780000,0x47e88b5⟩,⟨⟨851,1183,249,30922⟩,0x108708880000,0xc4f2a7606⟩⟩,
    ⟨18,⟨⟨221,306,68,1920⟩,0x4e346c0000,0xf032b8c⟩,⟨⟨952,1324,279,32132⟩,0x17270e900000,0x1350bb1fb5⟩⟩,
    ⟨24,⟨⟨212,294,65,3964⟩,0x44e9c40000,0xcc1a54f⟩,⟨⟨1115,1550,329,40307⟩,0x255cff880000,0x2473d5ffe4⟩⟩,
    ⟨32,⟨⟨261,362,82,4858⟩,0x826c0c0000,0x1db6eefa⟩,⟨⟨1463,2034,430,47252⟩,0x54106e900000,0x6b9d823520⟩⟩,
    ⟨36,⟨⟨246,341,75,52074⟩,0x6ae4280000,0x16e7d3b2⟩,⟨⟨1220,1696,357,83679⟩,0x309db61c0000,0x33e3754396⟩⟩,
    ⟨42,⟨⟨279,386,85,52418⟩,0x9b80980000,0x25892b87⟩,⟨⟨1240,1725,359,187144⟩,0x32a0cb700000,0x370899d961⟩⟩,
    ⟨54,⟨⟨534,740,167,4094⟩,0x44f1df00000,0x1ff6e1863⟩,⟨⟨2252,3131,661,71460⟩,0x131ef423c0000,0x25ab1ba8825⟩⟩,
    ⟨81,⟨⟨637,883,197,7247⟩,0x73e2ad80000,0x401d0f0c6⟩,⟨⟨3474,4830,1019,97667⟩,0x461aa92080000,0xd5013df2ef9⟩⟩,
    ⟨100,⟨⟨774,1072,239,8675⟩,0xcf60ca00000,0x8af950b98⟩,⟨⟨4170,5798,1223,118327⟩,0x7934721300000,0x1ba1a89b2ba1⟩⟩,
    ⟨135,⟨⟨1042,1443,329,10883⟩,0x201c60040000,0x1cf53a5560⟩,⟨⟨5487,7630,1607,156136⟩,0x113c22e7a00000,0x52bdbe618ec3⟩⟩]
  | .h7773 => [⟨0,⟨⟨11,15,3,128⟩,0x3500000,0x892⟩,⟨⟨20,28,4,262⟩,0xdc00000,0x4287⟩⟩,
    ⟨2,⟨⟨21,29,6,153⟩,0x13cc0000,0x609d⟩,⟨⟨38,53,9,383⟩,0x5d840000,0x33bc5⟩⟩,
    ⟨5,⟨⟨34,47,10,233⟩,0x4f100000,0x26533⟩,⟨⟨64,89,15,599⟩,0x1a3600000,0x17e10a⟩⟩,
    ⟨10,⟨⟨54,75,16,384⟩,0x12f140000,0xe9a95⟩,⟨⟨101,141,24,1006⟩,0x64f3c0000,0x91e8ba⟩⟩]
def fees : Band → P1_7.PrefixFees
  | .h2367 => ⟨0x16191042ba7373c,0x20ae8213be,0x389defe37419f,0x6efbc48253289a,0x1b11e40a2e68,0x20b01c0083c8⟩
  | .h2395 => ⟨0xc33fe826a42e0c,0x1875072084,0x2c90e2928ea82,0x4850b0b96b2e8b,0x14c406222984,0x175b6b005e2a⟩
  | .h7773 => ⟨0x26c061ed8d932,0xf71eac,0xe8fa600fdb4,0x7c3b971ead8,0x16df07a35,0xc17a00030c⟩
def retainedCap : Band → ℕ
  | .h2367 => 0x1e61bf08b0625dd
  | .h2395 => 0x2a5afd361b76701
  | .h7773 => 0x122c306579862
def highBound : Band → ℕ
  | .h2367 => 0x3ba6e7ae5c48d41
  | .h2395 => 0x3b435b25119564d
  | .h7773 => 0x3a5df6d8af60e

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

theorem height_cover {h : ℕ} (lo : 2342 ≤ h) (hi : h ≤ heightCap) :
    ∃ b, start b ≤ h ∧ h ≤ finish b := by
  by_cases h0 : h ≤ 2414
  · exact ⟨.h2367, lo, h0⟩
  by_cases h1 : h ≤ 7772
  · exact ⟨.h2395, by change 2415 ≤ h; omega, h1⟩
  exact ⟨.h7773, by change 7773 ≤ h; omega, hi⟩

theorem accounting (b : Band) :
    (fees b).loss + (fees b).point + (fees b).lowSeed + (fees b).lowJet +
       (fees b).fixedODE + (fees b).content + retainedCap b + 1 = highBound b ∧
       highBound b ≤ 268648601901894977 := by
  cases b <;> decide +kernel

end HighCore82219
