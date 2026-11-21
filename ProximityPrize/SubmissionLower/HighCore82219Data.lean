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
  | h2405
  deriving DecidableEq

open K1_14 (Shape shapeSum triangle slots)
def start : Band → ℕ
  | .h2405 => 2405
def finish : Band → ℕ
  | .h2405 => 2526
def terminal : Band → Bank
  | .h2405 => ⟨⟨7052,9807,2078,219723⟩,0x24c0a185540000,0xe2d5b7791e37⟩
def grades : Band → List Grade
  | .h2405 => [⟨393,219723⟩, ⟨386,219723⟩, ⟨380,219723⟩, ⟨373,219723⟩, ⟨365,219723⟩, ⟨357,219723⟩, ⟨349,219723⟩, ⟨341,219723⟩, ⟨331,219723⟩, ⟨322,219723⟩, ⟨311,219723⟩, ⟨299,219723⟩, ⟨285,219723⟩, ⟨270,219723⟩, ⟨253,219723⟩, ⟨233,219723⟩, ⟨212,219723⟩, ⟨188,219723⟩, ⟨162,219723⟩, ⟨134,219723⟩, ⟨104,219723⟩, ⟨71,219723⟩, ⟨37,219723⟩, ⟨1,219723⟩]
def stages : Band → List Stage
  | .h2405 => [⟨0, ⟨⟨73,101,22,818⟩,0x2e5640000,0x2f6f2a⟩, ⟨⟨353,491,103,11873⟩,0x12fc4600000,0x5e3742a9⟩⟩,
    ⟨1, ⟨⟨60,83,18,10262⟩,0x19fec0000,0x15f0f2⟩, ⟨⟨405,563,118,12714⟩,0x1c9714c0000,0xa26535f3⟩⟩,
    ⟨2, ⟨⟨109,151,33,781⟩,0x979280000,0xe74c1b⟩, ⟨⟨445,619,130,13789⟩,0x25f62dc0000,0xed5a05de⟩⟩,
    ⟨3, ⟨⟨122,169,38,826⟩,0xd80c80000,0x170ad54⟩, ⟨⟨473,659,138,15124⟩,0x2d836e40000,0x12ff82db2⟩⟩,
    ⟨5, ⟨⟨131,181,40,987⟩,0x106e580000,0x1dd3cf8⟩, ⟨⟨558,775,163,17196⟩,0x4aad7380000,0x246465872⟩⟩,
    ⟨8, ⟨⟨140,194,42,1321⟩,0x13bfdc0000,0x26a2eee⟩, ⟨⟨653,908,191,20857⟩,0x77a65000000,0x447811faa⟩⟩,
    ⟨13, ⟨⟨179,248,55,1639⟩,0x29b7600000,0x681fcb3⟩, ⟨⟨859,1195,253,26169⟩,0x111524d80000,0xcdfbb5b3b⟩⟩,
    ⟨18, ⟨⟨193,267,58,2515⟩,0x3355540000,0x895de88⟩, ⟨⟨1043,1451,305,31892⟩,0x1e61e4680000,0x1bcaea101e⟩⟩,
    ⟨25, ⟨⟨362,502,114,2124⟩,0x15ae1900000,0x6d68a9c9⟩, ⟨⟨1225,1703,357,41506⟩,0x310fd3780000,0x349473cb5b⟩⟩,
    ⟨29, ⟨⟨210,291,64,43105⟩,0x42b1ac0000,0xc32b568⟩, ⟨⟨1318,1839,385,47738⟩,0x3d329b940000,0x4765896c69⟩⟩,
    ⟨31, ⟨⟨295,409,90,3244⟩,0xb7d8100000,0x2f3b1229⟩, ⟨⟨1516,2105,443,46912⟩,0x5d1c55480000,0x7afe40f467⟩⟩,
    ⟨47, ⟨⟨402,559,122,4696⟩,0x1cd6b900000,0xa2dfd458⟩, ⟨⟨2123,2950,628,64726⟩,0x101e034e80000,0x1de23726e9e⟩⟩,
    ⟨60, ⟨⟨377,523,114,72955⟩,0x17bd5e40000,0x7cce7b05⟩, ⟨⟨2155,2994,634,95409⟩,0x10c9546a80000,0x1f9316168cb⟩⟩,
    ⟨63, ⟨⟨500,692,155,6243⟩,0x3841b080000,0x185234383⟩, ⟨⟨2696,3749,788,83251⟩,0x20b0925680000,0x4d21177bab1⟩⟩,
    ⟨88, ⟨⟨526,731,158,148418⟩,0x3fecfe00000,0x1d7121286⟩, ⟨⟨2811,3918,819,154657⟩,0x24f5ff3100000,0x5b99db6de2b⟩⟩,
    ⟨70, ⟨⟨425,590,130,204112⟩,0x22423840000,0xcb755a0e⟩, ⟨⟨2032,2827,594,201333⟩,0xe01986d40000,0x18f3217cfe1⟩⟩,
    ⟨105, ⟨⟨806,1116,251,9250⟩,0xeba01480000,0xa44b9ecd3⟩, ⟨⟨4291,5969,1261,130026⟩,0x844328b580000,0x1f12fe9a79ee⟩⟩,
    ⟨1, ⟨⟨80,111,24,906⟩,0x3c7300000,0x4451ef⟩, ⟨⟨380,530,100,31547⟩,0x15dc6d00000,0x7597b06c⟩⟩,
    ⟨2, ⟨⟨86,119,26,1008⟩,0x4b3780000,0x5a8245⟩, ⟨⟨547,764,141,31641⟩,0x3fe66d80000,0x1f060dc24⟩⟩,
    ⟨3, ⟨⟨91,126,27,1172⟩,0x57a300000,0x6fafa5⟩, ⟨⟨1081,1507,264,85217⟩,0x1d679b940000,0x1bfe368baa⟩⟩,
    ⟨4, ⟨⟨97,134,29,1284⟩,0x6a6580000,0x8f605a⟩, ⟨⟨664,925,200,15862⟩,0x809ed600000,0x4b52e2da2⟩⟩,
    ⟨6, ⟨⟨111,153,34,1436⟩,0xa15400000,0xf6b69e⟩, ⟨⟨494,688,140,23876⟩,0x32b0a2c0000,0x160efc81a⟩⟩,
    ⟨9, ⟨⟨129,179,39,1772⟩,0xf95600000,0x1c3d3dd⟩, ⟨⟨701,976,192,28382⟩,0x8cad28c0000,0x56ac98d52⟩⟩,
    ⟨13, ⟨⟨161,223,49,1963⟩,0x1e3a480000,0x43d826b⟩, ⟨⟨996,1388,254,91998⟩,0x17ce40840000,0x14de8d1a33⟩⟩,
    ⟨16, ⟨⟨168,233,50,2907⟩,0x21bc440000,0x4f48465⟩, ⟨⟨1122,1566,343,30727⟩,0x271c0f900000,0x26eb47ca19⟩⟩,
    ⟨13, ⟨⟨190,263,59,1539⟩,0x3235480000,0x849a735⟩, ⟨⟨1811,2518,553,32225⟩,0xa40e21480000,0x1042a2fc6be⟩⟩,
    ⟨28, ⟨⟨249,346,77,3732⟩,0x7002580000,0x187d9080⟩, ⟨⟨2394,3335,706,45467⟩,0x170d016500000,0x309550b3c97⟩⟩,
    ⟨31, ⟨⟨253,351,80,5098⟩,0x776e8c0000,0x1a683d4b⟩, ⟨⟨1126,1572,307,164949⟩,0x243638180000,0x241fd7a6b1⟩⟩,
    ⟨20, ⟨⟨266,369,82,1909⟩,0x8812100000,0x1f9950b6⟩, ⟨⟨1022,1428,311,39540⟩,0x1d7761500000,0x1ace076bd3⟩⟩,
    ⟨43, ⟨⟨316,439,98,7907⟩,0xe4864c0000,0x3f4c6dc0⟩, ⟨⟨2509,3505,762,60936⟩,0x1b224cb7c0000,0x3c82694be91⟩⟩]
def fees : Band → P1_7.PrefixFees
  | .h2405 => ⟨0xcab93b5d870ff8,0x1799855d06,0x2d079b429f336,6436,0x14e8949751f0,0x1897ed006326⟩
def retainedCap : Band → ℕ
  | .h2405 => 0x2eef5ba4edcafbf
def highBound : Band → ℕ
  | .h2405 => 0x3bcad077baade2e

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

theorem accounting (b : Band) :
    (fees b).loss + (fees b).point + (fees b).lowSeed + (fees b).lowJet +
       (fees b).fixedODE + (fees b).content + retainedCap b + 1 = highBound b ∧
       highBound b ≤ 269280325386559022 := by
  cases b <;> decide +kernel

end HighCore82219
