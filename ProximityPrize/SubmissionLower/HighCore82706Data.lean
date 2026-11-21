import ProximityPrize.SubmissionLower.GoldBranch7

set_option Elab.async false
set_option autoImplicit true
set_option maxRecDepth 18000

namespace HighCore82706

abbrev agreement : ℕ := 179438
abbrev heightCap : ℕ := 34339
abbrev Bank := P1_7.Bank
abbrev Stage := P1_7.Stage
abbrev Grade := P1_7.Grade
abbrev debit := P1_7.debit

inductive Band where
  | h3640 | h3690 | h10300
  deriving DecidableEq

open K1_14 (Shape shapeSum triangle slots)
def start : Band → ℕ
  | .h3640 => 3640
  | .h3690 => 3690
  | .h10300 => 10300
def finish : Band → ℕ
  | .h3640 => 3689
  | .h3690 => 10299
  | .h10300 => 34339
def terminal : Band → Bank
  | .h3640 => ⟨⟨6400,8911,1880,193282⟩,0x1b6887c6100000,0x9a1ce5e33829⟩
  | .h3690 => ⟨⟨6400,8911,1880,193282⟩,0x1b6887c6100000,0x9a1ce5e33829⟩
  | .h10300 => ⟨⟨124,173,32,804⟩,0xc4fd80000,0x15c66e5⟩
def grades : Band → List Grade
  | .h3640 => [⟨384,193282⟩, ⟨378,193282⟩, ⟨371,193282⟩, ⟨364,193282⟩, ⟨357,193282⟩, ⟨350,193282⟩, ⟨342,193282⟩, ⟨333,193282⟩, ⟨325,193282⟩, ⟨315,193282⟩, ⟨305,193282⟩, ⟨293,193282⟩, ⟨281,193282⟩, ⟨266,193282⟩, ⟨250,193282⟩, ⟨231,193282⟩, ⟨210,193282⟩, ⟨188,193282⟩, ⟨163,193282⟩, ⟨136,193282⟩, ⟨107,193282⟩, ⟨77,193282⟩, ⟨44,193282⟩, ⟨9,193282⟩]
  | .h3690 => [⟨347,193282⟩, ⟨341,193282⟩, ⟨334,193282⟩, ⟨327,193282⟩, ⟨320,193282⟩, ⟨312,193282⟩, ⟨304,193282⟩, ⟨295,193282⟩, ⟨286,193282⟩, ⟨276,193282⟩, ⟨264,193282⟩, ⟨251,193282⟩, ⟨236,193282⟩, ⟨219,193282⟩, ⟨199,193282⟩, ⟨177,193282⟩, ⟨153,193282⟩, ⟨126,193282⟩, ⟨98,193282⟩, ⟨67,193282⟩, ⟨34,193282⟩]
  | .h10300 => [⟨26,804⟩, ⟨24,804⟩, ⟨23,804⟩, ⟨21,804⟩, ⟨18,804⟩, ⟨13,804⟩, ⟨8,804⟩, ⟨1,804⟩]
def stages : Band → List Stage
  | .h3640 => [⟨0, ⟨⟨60,83,18,782⟩,0x19fec0000,0x15f0f2⟩, ⟨⟨261,363,75,7226⟩,0x79f4900000,0x1bfccd5c⟩⟩,
    ⟨1, ⟨⟨70,97,21,762⟩,0x28d4c0000,0x284e2c⟩, ⟨⟨311,432,91,8476⟩,0xd08e300000,0x38c64aa5⟩⟩,
    ⟨2, ⟨⟨76,105,23,847⟩,0x345100000,0x3777f9⟩, ⟨⟨320,445,93,9740⟩,0xe1ed2c0000,0x3f7f129a⟩⟩,
    ⟨4, ⟨⟨86,119,26,1074⟩,0x4b3780000,0x5a8245⟩, ⟨⟨393,546,113,11948⟩,0x19df1880000,0x8e509307⟩⟩,
    ⟨5, ⟨⟨98,136,30,1004⟩,0x6f9680000,0x9a30e6⟩, ⟨⟨425,591,124,13297⟩,0x210e0940000,0xc536b22c⟩⟩,
    ⟨6, ⟨⟨105,145,32,1076⟩,0x885f40000,0xc69177⟩, ⟨⟨456,634,132,14398⟩,0x288d8880000,0x1035df3b1⟩⟩,
    ⟨10, ⟨⟨124,172,38,1518⟩,0xe00240000,0x1860091⟩, ⟨⟨558,776,163,20272⟩,0x4aad7380000,0x248b0bcd0⟩⟩,
    ⟨16, ⟨⟨171,237,52,1767⟩,0x2422280000,0x5644c7b⟩, ⟨⟨761,1058,225,28331⟩,0xbebc9480000,0x7f1ef5405⟩⟩,
    ⟨18, ⟨⟨174,241,53,2157⟩,0x26190c0000,0x5c59f4f⟩, ⟨⟨796,1107,231,30889⟩,0xd723df00000,0x9611aacf3⟩⟩,
    ⟨24, ⟨⟨213,295,65,2670⟩,0x45a3e80000,0xce56381⟩, ⟨⟨1021,1420,296,37091⟩,0x1c50c24c0000,0x1954762b9b⟩⟩,
    ⟨32, ⟨⟨237,328,72,5354⟩,0x5f65ec0000,0x1398c9e3⟩, ⟨⟨940,1307,273,128583⟩,0x1622c7240000,0x1237cc25ed⟩⟩,
    ⟨36, ⟨⟨302,418,94,3497⟩,0xc828a00000,0x345f569a⟩, ⟨⟨1355,1884,393,54587⟩,0x42213b080000,0x4e6a4b287f⟩⟩,
    ⟨42, ⟨⟨284,393,87,9440⟩,0xa4a4900000,0x287b7ed9⟩, ⟨⟨1141,1587,334,267594⟩,0x27caafcc0000,0x27ca1d088b⟩⟩,
    ⟨54, ⟨⟨417,578,129,5272⟩,0x20a4b080000,0xbd52fe61⟩, ⟨⟨1895,2635,547,78987⟩,0xb40a7fd00000,0x12a87aa5766⟩⟩,
    ⟨81, ⟨⟨616,853,192,7208⟩,0x69719d00000,0x383c9a9ad⟩, ⟨⟨2651,3686,769,120834⟩,0x1ee6add680000,0x47a8357cdda⟩⟩,
    ⟨100, ⟨⟨753,1043,235,8658⟩,0xc085f900000,0x7d9526018⟩, ⟨⟨3390,4714,997,139728⟩,0x41467c9ac0000,0xc1a6e7a2433⟩⟩]
  | .h3690 => [⟨0, ⟨⟨60,83,18,782⟩,0x19fec0000,0x15f0f2⟩, ⟨⟨261,363,75,6405⟩,0x79f4900000,0x1bfccd5c⟩⟩,
    ⟨1, ⟨⟨70,97,21,762⟩,0x28d4c0000,0x284e2c⟩, ⟨⟨311,432,91,7396⟩,0xd08e300000,0x38c64aa5⟩⟩,
    ⟨2, ⟨⟨76,105,23,847⟩,0x345100000,0x3777f9⟩, ⟨⟨320,445,93,8377⟩,0xe1ed2c0000,0x3f7f129a⟩⟩,
    ⟨4, ⟨⟨86,119,26,1074⟩,0x4b3780000,0x5a8245⟩, ⟨⟨393,546,113,10296⟩,0x19df1880000,0x8e509307⟩⟩,
    ⟨5, ⟨⟨98,136,30,1004⟩,0x6f9680000,0x9a30e6⟩, ⟨⟨425,591,124,11429⟩,0x210e0940000,0xc536b22c⟩⟩,
    ⟨6, ⟨⟨105,145,32,1076⟩,0x885f40000,0xc69177⟩, ⟨⟨456,634,132,12364⟩,0x288d8880000,0x1035df3b1⟩⟩,
    ⟨10, ⟨⟨124,172,38,1518⟩,0xe00240000,0x1860091⟩, ⟨⟨558,776,163,17085⟩,0x4aad7380000,0x248b0bcd0⟩⟩,
    ⟨16, ⟨⟨171,237,52,1767⟩,0x2422280000,0x5644c7b⟩, ⟨⟨761,1058,225,23848⟩,0xbebc9480000,0x7f1ef5405⟩⟩,
    ⟨18, ⟨⟨174,241,53,2157⟩,0x26190c0000,0x5c59f4f⟩, ⟨⟨796,1107,231,25818⟩,0xd723df00000,0x9611aacf3⟩⟩,
    ⟨24, ⟨⟨213,295,65,2576⟩,0x45a3e80000,0xce56381⟩, ⟨⟨1021,1420,296,31370⟩,0x1c50c24c0000,0x1954762b9b⟩⟩,
    ⟨32, ⟨⟨237,328,72,4767⟩,0x5f65ec0000,0x1398c9e3⟩, ⟨⟨940,1307,273,76164⟩,0x1622c7240000,0x1237cc25ed⟩⟩,
    ⟨36, ⟨⟨302,418,94,3292⟩,0xc828a00000,0x345f569a⟩, ⟨⟨1355,1884,393,45460⟩,0x42213b080000,0x4e6a4b287f⟩⟩,
    ⟨42, ⟨⟨284,393,87,8000⟩,0xa4a4900000,0x287b7ed9⟩, ⟨⟨1141,1587,334,123304⟩,0x27caafcc0000,0x27ca1d088b⟩⟩,
    ⟨54, ⟨⟨417,578,129,4945⟩,0x20a4b080000,0xbd52fe61⟩, ⟨⟨1895,2635,547,65458⟩,0xb40a7fd00000,0x12a87aa5766⟩⟩,
    ⟨81, ⟨⟨616,853,192,6800⟩,0x69719d00000,0x383c9a9ad⟩, ⟨⟨2651,3686,769,98671⟩,0x1ee6add680000,0x47a8357cdda⟩⟩,
    ⟨100, ⟨⟨753,1043,235,8181⟩,0xc085f900000,0x7d9526018⟩, ⟨⟨3390,4714,997,116266⟩,0x41467c9ac0000,0xc1a6e7a2433⟩⟩]
  | .h10300 => [⟨0, ⟨⟨11,15,3,125⟩,0x3500000,2194⟩, ⟨⟨20,28,4,256⟩,0xdc00000,17031⟩⟩,
    ⟨2, ⟨⟨21,29,6,151⟩,0x13cc0000,24733⟩, ⟨⟨38,53,9,375⟩,0x5d840000,211909⟩⟩,
    ⟨5, ⟨⟨34,47,10,230⟩,0x4f100000,156979⟩, ⟨⟨64,89,15,587⟩,0x1a3600000,0x17e10a⟩⟩,
    ⟨10, ⟨⟨54,75,16,378⟩,0x12f140000,957077⟩, ⟨⟨101,141,24,985⟩,0x64f3c0000,0x91e8ba⟩⟩]
def fees : Band → P1_7.PrefixFees
  | .h3640 => ⟨0x792aa06ba6a26c,0x13ae0bf6f1,0x20bdd061d1db7,0x2515085a6ecdb7,0x814a5bafddc,0xf84b8003e90⟩
  | .h3690 => ⟨0x644dca284e6830,0xe623fa48c,0x1f8c5821b866c,0x2453eb3753f96d,0x87a1d3baf90,0xded6d003826⟩
  | .h10300 => ⟨0x25f3ecf8ea240,0xec09e1,0xe395400f361,0x779364c1f6d,0x1711b2031,0xbd030002fa⟩
def retainedCap : Band → ℕ
  | .h3640 => 0x2c858dc62c4b2d3
  | .h3690 => 0x20ae7e82391a8cc
  | .h10300 => 0x11b5d2b231a2a
def highBound : Band → ℕ
  | .h3640 => 0x368bc0f3abe740b
  | .h3690 => 0x29598d8f1cb1d18
  | .h10300 => 0x3910cfa05fc45
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

theorem height_cover {h : ℕ} (lo : 3640 ≤ h) (hi : h ≤ heightCap) :
    ∃ b, start b ≤ h ∧ h ≤ finish b := by
  by_cases h0 : h ≤ 3689
  · exact ⟨.h3640, lo, h0⟩
  by_cases h1 : h ≤ 10299
  · exact ⟨.h3690, by change 3690 ≤ h; omega, h1⟩
  exact ⟨.h10300, by change 10300 ≤ h; omega, hi⟩

theorem accounting (b : Band) :
    (fees b).loss + (fees b).point + (fees b).lowSeed + (fees b).lowJet +
       (fees b).fixedODE + (fees b).content + retainedCap b + 1 = highBound b ∧
       highBound b ≤ 245652953287783435 := by
  cases b <;> decide +kernel

end HighCore82706
