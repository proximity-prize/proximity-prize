import ProximityPrize.SubmissionLower.GoldBranch7

set_option Elab.async false
set_option autoImplicit true
set_option maxRecDepth 18000

namespace Rect52Prefix

abbrev agreement : ℕ := 179905
abbrev heightCap : ℕ := 33463
abbrev Bank := P1_7.Bank
abbrev Stage := P1_7.Stage
abbrev Grade := P1_7.Grade
abbrev debit := P1_7.debit

inductive Band where
  | h2391
  deriving DecidableEq

open K1_14 (Shape shapeSum triangle slots)
def start : Band → ℕ
  | .h2391 => 2391
def finish : Band → ℕ
  | .h2391 => 2451
def terminal : Band → Bank
  | .h2391 => ⟨⟨6220,8648,1834,341710⟩,0x193baf9f5c0000,0x8944c1334160⟩
def grades : Band → List Grade
  | .h2391 => []
def stages : Band → List Stage
  | .h2391 => [⟨0, ⟨⟨70,97,21,1037⟩,0x28d4c0000,0x284e2c⟩, ⟨⟨381,530,111,16161⟩,0x17d1c400000,0x7f95aba6⟩⟩,
    ⟨1, ⟨⟨77,107,23,1144⟩,0x35da00000,0x3ae575⟩, ⟨⟨401,558,116,18864⟩,0x1b9a9440000,0x9bbb4f84⟩⟩,
    ⟨2, ⟨⟨83,115,25,1272⟩,0x439080000,0x4ed4ac⟩, ⟨⟨485,675,142,18325⟩,0x312f66c0000,0x14facc9aa⟩⟩,
    ⟨3, ⟨⟨91,126,27,1359⟩,0x57a300000,0x6fafa5⟩, ⟨⟨535,745,155,19781⟩,0x416e7300000,0x1ed40d93b⟩⟩,
    ⟨5, ⟨⟨106,147,32,1473⟩,0x8b45c0000,0xcf7010⟩, ⟨⟨569,791,166,24153⟩,0x4f174840000,0x276a61df4⟩⟩,
    ⟨7, ⟨⟨120,166,37,1642⟩,0xcc31c0000,0x1553865⟩, ⟨⟨671,933,196,26304⟩,0x81a8f600000,0x4c3aaf76c⟩⟩,
    ⟨10, ⟨⟨142,197,43,1905⟩,0x14bde80000,0x294fec6⟩, ⟨⟨820,1141,240,30009⟩,0xecaf4280000,0xaa63e2113⟩⟩,
    ⟨16, ⟨⟨169,235,50,3510⟩,0x222f040000,0x517adc3⟩, ⟨⟨1033,1435,304,39778⟩,0x1da95f340000,0x1ac0470697⟩⟩,
    ⟨13, ⟨⟨206,285,64,1576⟩,0x3fe4a40000,0xb68effd⟩, ⟨⟨1043,1452,305,33006⟩,0x1e61e4680000,0x1bdaae9c57⟩⟩,
    ⟨23, ⟨⟨207,287,64,4753⟩,0x4096600000,0xbab2d1e⟩, ⟨⟨1319,1833,385,50283⟩,0x3d4d25c80000,0x46a696e4a8⟩⟩,
    ⟨32, ⟨⟨261,362,80,6360⟩,0x8008bc0000,0x1d282567⟩, ⟨⟨1679,2333,490,63914⟩,0x7e5359c00000,0xb9375c1e10⟩⟩,
    ⟨35, ⟨⟨259,359,79,15141⟩,0x7cac400000,0x1c1d91ae⟩, ⟨⟨1421,1980,416,99341⟩,0x4ccddb6c0000,0x602dc09b83⟩⟩,
    ⟨42, ⟨⟨293,407,91,24319⟩,0xb694500000,0x2ee3dfbb⟩, ⟨⟨1507,2100,445,163749⟩,0x5c32a3980000,0x7a7ca066ee⟩⟩,
    ⟨49, ⟨⟨441,612,138,4746⟩,0x26ebe240000,0xefa996b5⟩, ⟨⟨2121,2955,615,101012⟩,0xfd3f8e600000,0x1d8f26a3eb9⟩⟩,
    ⟨76, ⟨⟨599,832,186,7956⟩,0x60b2db00000,0x32a5068be⟩, ⟨⟨3373,4700,987,132042⟩,0x400ced8500000,0xbe4d2da6f3f⟩⟩,
    ⟨114, ⟨⟨925,1283,285,9979⟩,0x161084780000,0x11bf980276⟩, ⟨⟨5067,7037,1492,184432⟩,0xda1220ce80000,0x3c2eefe70454⟩⟩,
    ⟨158, ⟨⟨1161,1612,364,15612⟩,0x2c2938540000,0x2cbc69abd7⟩, ⟨⟨6803,9479,1991,251561⟩,0x20d2fc74a00000,0xc4a19dc9e22d⟩⟩]
def fees : Band → P1_7.PrefixFees
  | .h2391 => ⟨0x16013383186d14e,0x2cb7c9d4d3,0x39889ed3e5f15,6302,0x1af684b6c3b8,0x2153d200865c⟩
def retainedCap : Band → ℕ
  | .h2391 => 0x25624d8f6f39d27
def highBound : Band → ℕ
  | .h2391 => 0x3ba0d12243a0510
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
       highBound b ≤ 271879479853429943 := by
  cases b <;> decide +kernel

end Rect52Prefix
