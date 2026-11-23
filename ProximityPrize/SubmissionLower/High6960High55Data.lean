import ProximityPrize.SubmissionLower.GoldBranch7

set_option Elab.async false
set_option autoImplicit true
set_option maxRecDepth 18000

namespace High6960High55

abbrev agreement:ℕ:=179827
abbrev heightCap:ℕ:=34339
abbrev Bank:=P1_7.Bank
abbrev Stage:=P1_7.Stage
abbrev Grade:=P1_7.Grade
abbrev debit:=P1_7.debit

inductive Band where
  | h2570 | h8100
  deriving DecidableEq

open K1_14 (Shape shapeSum triangle slots)
def start : Band → ℕ
  | .h2570 => 2696
  | .h8100 => 8349
def finish : Band → ℕ
  | .h2570 => 8348
  | .h8100 => 34339
def terminal : Band → Bank
  | .h2570 => ⟨⟨7550,10506,2218,234728⟩,0x2cfea55aa80000,0x129e297a45c0c⟩
  | .h8100 => ⟨⟨124,173,32,804⟩,0xc4fd80000,0x15c66e5⟩
def grades : Band → List Grade
  | .h2570 => [⟨348,234728⟩,⟨341,234728⟩,⟨334,234728⟩,⟨327,234728⟩,⟨320,234728⟩,⟨312,234728⟩,⟨303,234728⟩,⟨294,234728⟩,⟨284,234728⟩,⟨273,234728⟩,⟨261,234728⟩,⟨247,234728⟩,⟨231,234728⟩,⟨212,234728⟩,⟨191,234728⟩,⟨167,234728⟩,⟨141,234728⟩,⟨113,234728⟩,⟨82,234728⟩,⟨49,234728⟩,⟨14,234728⟩]
  | .h8100 => [⟨25,804⟩,⟨24,804⟩,⟨22,804⟩,⟨20,804⟩,⟨17,804⟩,⟨13,804⟩,⟨7,804⟩,⟨0,804⟩]
def stages : Band → List Stage
  | .h2570 => [⟨0, ⟨⟨73,101,22,696⟩,0x2e5640000,0x2f6f2a⟩, ⟨⟨352,489,103,9135⟩,0x12dda700000,0x5cfd94a5⟩⟩,
    ⟨1,⟨⟨78,108,24,793⟩,0x392740000,0x3e9e8f⟩,⟨⟨345,480,101,10666⟩,0x11c61f80000,0x564a51c0⟩⟩,
    ⟨2,⟨⟨86,119,26,856⟩,0x4b3780000,0x5a8245⟩,⟨⟨385,535,112,11561⟩,0x188bf840000,0x84679137⟩⟩,
    ⟨3,⟨⟨94,130,29,908⟩,0x633bc0000,0x822d2c⟩,⟨⟨411,572,120,12709⟩,0x1dec1a80000,0xad1e0c80⟩⟩,
    ⟨4,⟨⟨102,141,31,972⟩,0x7cec00000,0xb15384⟩,⟨⟨438,609,128,13874⟩,0x2436d340000,0xde912dc3⟩⟩,
    ⟨5,⟨⟨108,150,33,1053⟩,0x948040000,0xe271e9⟩,⟨⟨522,726,153,14099⟩,0x3d548e40000,0x1c16ef1c7⟩⟩,
    ⟨6,⟨⟨108,149,33,1272⟩,0x948040000,0xdda994⟩,⟨⟨570,792,167,14983⟩,0x4fc3e700000,0x27c2e15db⟩⟩,
    ⟨10,⟨⟨142,197,43,1442⟩,0x14bde80000,0x294fec6⟩,⟨⟨696,968,204,19042⟩,0x910a3980000,0x5884788a7⟩⟩,
    ⟨16,⟨⟨163,226,50,2506⟩,0x1f8a780000,0x47e88b5⟩,⟨⟨851,1183,249,25796⟩,0x108708880000,0xc4f2a7606⟩⟩,
    ⟨18,⟨⟨221,306,68,1783⟩,0x4e346c0000,0xf032b8c⟩,⟨⟨952,1324,279,27241⟩,0x17270e900000,0x1350bb1fb5⟩⟩,
    ⟨24,⟨⟨212,294,65,3390⟩,0x44e9c40000,0xcc1a54f⟩,⟨⟨1115,1550,329,34056⟩,0x255cff880000,0x2473d5ffe4⟩⟩,
    ⟨32,⟨⟨261,362,82,4217⟩,0x826c0c0000,0x1db6eefa⟩,⟨⟨1463,2034,430,40812⟩,0x54106e900000,0x6b9d823520⟩⟩,
    ⟨36,⟨⟨246,341,75,18805⟩,0x6ae4280000,0x16e7d3b2⟩,⟨⟨1220,1696,357,62059⟩,0x309db61c0000,0x33e3754396⟩⟩,
    ⟨42,⟨⟨279,386,85,21222⟩,0x9b80980000,0x25892b87⟩,⟨⟨1240,1725,359,104847⟩,0x32a0cb700000,0x370899d961⟩⟩,
    ⟨54,⟨⟨534,740,167,3917⟩,0x44f1df00000,0x1ff6e1863⟩,⟨⟨2252,3131,661,62291⟩,0x131ef423c0000,0x25ab1ba8825⟩⟩,
    ⟨81,⟨⟨637,883,197,6816⟩,0x73e2ad80000,0x401d0f0c6⟩,⟨⟨3474,4830,1019,86750⟩,0x461aa92080000,0xd5013df2ef9⟩⟩,
    ⟨100,⟨⟨774,1072,239,8193⟩,0xcf60ca00000,0x8af950b98⟩,⟨⟨4170,5798,1223,105125⟩,0x7934721300000,0x1ba1a89b2ba1⟩⟩,
    ⟨135,⟨⟨1042,1443,329,10350⟩,0x201c60040000,0x1cf53a5560⟩,⟨⟨5487,7630,1607,138831⟩,0x113c22e7a00000,0x52bdbe618ec3⟩⟩]
  | .h8100 => [⟨0, ⟨⟨11,15,3,125⟩,0x3500000,2194⟩, ⟨⟨20,28,4,256⟩,0xdc00000,17031⟩⟩,
    ⟨2,⟨⟨21,29,6,151⟩,0x13cc0000,24733⟩,⟨⟨38,53,9,375⟩,0x5d840000,211909⟩⟩,
    ⟨5,⟨⟨34,47,10,230⟩,0x4f100000,156979⟩,⟨⟨64,89,15,587⟩,0x1a3600000,0x17e10a⟩⟩,
    ⟨10,⟨⟨54,75,16,378⟩,0x12f140000,957077⟩,⟨⟨101,141,24,985⟩,0x64f3c0000,0x91e8ba⟩⟩]
def fees : Band → P1_7.PrefixFees
  | .h2570 => ⟨43774020910186239,89226851686,671227926531827,14998968604578829,22939363546052,20946974952654⟩
  | .h8100 => ⟨667673328253744,15469025,15639385273185,8199408181613,6179174781,811799151354⟩
def retainedCap : Band → ℕ
  | .h2570 => 145769298686796491
  | .h8100 => 319279348965197
def highBound : Band → ℕ
  | .h2570 => 205257491693443779
  | .h8100 => 1011609464468900
def subbank (b : Band) (g : Grade) : Bank :=
  let t:=terminal b
  { t with shape := { t.shape with U:=g.slots } }

abbrev GradeIndex (b:Band):=Fin (grades b).length

def Listed (b : Band) (t : Bank) : Prop :=
  t = terminal b ∨ (∃ s ∈ stages b, t = s.free ∨ t = s.moving) ∨
    ∃ i:GradeIndex b,t=subbank b ((grades b).get i)

abbrev Test (b:Band):=Option (GradeIndex b)

def tested (b : Band) : Test b → Bank
  | none => terminal b
  | some i => subbank b ((grades b).get i)

def threshold (b : Band) : Test b → ℕ
  | none => (grades b).length+1
  | some i => i.val+1

def seedThreshold (b : Band) : Test b → ℕ
  | none => 0
  | some i => ((grades b).get i).seedCap+1

def jointGain (h : ℕ) (s : Shape) (E v : ℕ) : ℕ :=
  shapeSum s fun q j =>
    let g:=(q-j)/E
    let x:=s.m*agreement+j - q*(131071-h)
    let c:=fun a => slots s.U (a*v)
    (∑ a ∈ Finset.range g, (c a - c (a+1)) * (x - 2*h*(j+a))) +
      c g*(x - 2*h*(j+g))

def cutoffCount (h r : ℕ) (s : Shape) : ℕ :=
  s.m*agreement - 2*h*r

def rawWidth (h r : ℕ) (s : Shape) (q j : ℕ) : ℕ :=
  cutoffCount h r s+j - q*(131071 - h)

def WidthGuard (h r : ℕ) (s : Shape) : Prop :=
  s.B*(131071-h) < cutoffCount h r s

def gain (h r : ℕ) (s : Shape) (mode : ℕ) : ℕ :=
  triangle s.U*shapeSum s (fun q j => rawWidth h r s q j - mode*(2*h*j))

theorem height_cover {h : ℕ} (lo : 2696 ≤ h) (hi : h ≤ heightCap) :
    ∃ b,start b≤h ∧ h≤finish b:=by
  by_cases h0:h < 8349
  · exact ⟨.h2570,lo,by change h≤8348; omega⟩
  · exact ⟨.h8100,by change 8349≤h; omega,hi⟩

theorem accounting (b : Band) :
    (fees b).loss + (fees b).point + (fees b).lowSeed + (fees b).lowJet +
       (fees b).fixedODE+(fees b).content+retainedCap b+1=highBound b ∧
       highBound b≤272515177455741613:=by
  cases b <;> decide +kernel

end High6960High55
