import ProximityPrize.SubmissionLower.GoldBranch7

set_option Elab.async false
set_option autoImplicit true
set_option maxRecDepth 18000

namespace Peer653NativePrefix

abbrev agreement : ℕ := 179896
abbrev heightCap : ℕ := 33463
abbrev Bank := P1_7.Bank
abbrev Stage := P1_7.Stage
abbrev Grade := P1_7.Grade
abbrev debit := P1_7.debit

inductive Band where
  | h2390
  deriving DecidableEq

open K1_14 (Shape shapeSum triangle slots)
def start : Band → ℕ
  | .h2390 => 2390
def finish : Band → ℕ
  | .h2390 => 2526
abbrev terminalCredit : ℕ := 61490328644000

def terminal : Band → Bank
  | .h2390 => ⟨⟨4625,6431,1364,373000⟩,0xa60d3e1440000,0x29ff0aaee26a⟩
def grades : Band → List Grade
  | .h2390 => []
def stages : Band → List Stage
  | .h2390 => [⟨0, ⟨⟨76,105,23,899⟩,0x345100000,0x3777f9⟩, ⟨⟨437,608,128,16678⟩,0x2407b5c0000,0xdd657d32⟩⟩,
    ⟨1, ⟨⟨83,115,25,996⟩,0x439080000,0x4ed4ac⟩, ⟨⟨436,606,128,19877⟩,0x23d8b880000,0xdb115372⟩⟩,
    ⟨2, ⟨⟨92,127,28,1052⟩,0x5c3600000,0x75b415⟩, ⟨⟨508,706,149,20376⟩,0x389233c0000,0x19280bd7d⟩⟩,
    ⟨3, ⟨⟨99,137,30,1144⟩,0x722180000,0x9dd5af⟩, ⟨⟨492,686,144,24822⟩,0x33533580000,0x1656b0db4⟩⟩,
    ⟨4, ⟨⟨107,148,33,1209⟩,0x917680000,0xd8f2fa⟩, ⟨⟨525,731,154,26968⟩,0x3e6d7fc0000,0x1cdc7da38⟩⟩,
    ⟨5, ⟨⟨116,161,35,1280⟩,0xb5c380000,0x128bb48⟩, ⟨⟨642,892,188,25188⟩,0x71d1af40000,0x3fe068fa5⟩⟩,
    ⟨7, ⟨⟨126,175,39,1531⟩,0xec9f00000,0x1a458a5⟩, ⟨⟨685,952,201,29905⟩,0x8a677880000,0x52f0bdb9b⟩⟩,
    ⟨10, ⟨⟨142,197,43,2002⟩,0x14bde80000,0x294fec6⟩, ⟨⟨865,1202,254,33182⟩,0x1166fe340000,0xd28832ce8⟩⟩,
    ⟨16, ⟨⟨171,237,50,3773⟩,0x2316e80000,0x53b7f45⟩, ⟨⟨1014,1412,298,46976⟩,0x1c0729180000,0x1901657cf3⟩⟩,
    ⟨10, ⟨⟨178,247,55,1424⟩,0x2932d00000,0x66c8fdf⟩, ⟨⟨792,1101,233,35699⟩,0xd623cb40000,0x947787094⟩⟩,
    ⟨20, ⟨⟨250,347,78,2217⟩,0x721cb80000,0x18f6d6a4⟩, ⟨⟨1302,1815,383,49502⟩,0x3b50b1000000,0x442ac5ba92⟩⟩,
    ⟨32, ⟨⟨261,362,81,6848⟩,0x813b280000,0x1d6fb003⟩, ⟨⟨1459,2035,429,91441⟩,0x536744d80000,0x6b96ecc888⟩⟩,
    ⟨31, ⟨⟨345,478,108,2973⟩,0x12b1e340000,0x59a98629⟩, ⟨⟨1604,2235,472,73480⟩,0x6edb04b80000,0x9cb2a062f8⟩⟩,
    ⟨44, ⟨⟨376,522,118,5298⟩,0x183833c0000,0x7f6275d9⟩, ⟨⟨2253,3142,664,91156⟩,0x1334cd7ac0000,0x263b0eab16b⟩⟩,
    ⟨73, ⟨⟨599,831,188,7378⟩,0x617b2300000,0x32de21d13⟩, ⟨⟨3486,4863,1027,139224⟩,0x4711f2a780000,0xdb0e8041cee⟩⟩,
    ⟨76, ⟨⟨498,692,155,27147⟩,0x37c11c80000,0x185234383⟩, ⟨⟨2760,3850,812,234140⟩,0x233f7cff80000,0x5601e71ab3f⟩⟩,
    ⟨103, ⟨⟨809,1126,252,10229⟩,0xee4ed940000,0xa99a27482⟩, ⟨⟨4774,6667,1405,189186⟩,0xb6532fbfc0000,0x304357eb723c⟩⟩]
def fees : Band → P1_7.PrefixFees
  | .h2390 => ⟨0x19eea9eccfe2119,0x2d91a8a382,0x39b8dd937a16c,7409,0xfb1b3506062,0x220fd7008952⟩
def retainedCap : Band → ℕ
  | .h2390 => 0x21e9411009fcbc1
def highBound : Band → ℕ
  | .h2390 => 0x3c14c2cc2cf386e
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
       highBound b ≤ 270581207749572718 := by
  cases b <;> decide +kernel

end Peer653NativePrefix
