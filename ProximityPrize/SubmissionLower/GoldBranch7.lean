import ProximityPrize.SubmissionLower.UpperBranch3
import ProximityPrize.SubmissionLower.UpperBranch5
import ProximityPrize.SubmissionLower.UpperBranch7
set_option Elab.async false
set_option autoImplicit true
section
namespace P3_7
open P3 (HighBand)
abbrev Bank := P1_7.Bank
abbrev Stage := P1_7.Stage
abbrev Grade := P1_7.Grade
def terminal : HighBand → Bank
  | .h2274 => ⟨⟨6600,9172,1952,211000⟩,0x1e372113d00000,0xae27f29bc6cc⟩
  | .h2294 => ⟨⟨7550,10506,2218,234728⟩,0x2cfea55aa80000,0x129e297a45c0c⟩
  | .h7773 => ⟨⟨124,173,32,946⟩,0xc4fd80000,22832869⟩
def stages : HighBand → List Stage
  | .h2274 =>
    [⟨0, ⟨⟨76,105,23,862⟩,0x345100000,3635193⟩, ⟨⟨359,499,105,11883⟩,0x14006680000,0x64b8343e⟩⟩,
     ⟨1, ⟨⟨80,111,24,1024⟩,0x3c7300000,4477423⟩, ⟨⟨356,495,104,14432⟩,0x137d3580000,0x616d5567⟩⟩,
     ⟨2, ⟨⟨90,125,27,1032⟩,0x558480000,7136131⟩, ⟨⟨391,543,114,15483⟩,0x19c04900000,0x8cc85625⟩⟩,
     ⟨3, ⟨⟨99,137,30,1063⟩,0x722180000,10343855⟩, ⟨⟨429,596,126,16288⟩,0x222a41c0000,0xcd26d8f5⟩⟩,
     ⟨4, ⟨⟨106,147,32,1146⟩,0x8b45c0000,13594640⟩, ⟨⟨483,671,142,16629⟩,0x30bbe980000,0x14954ceae⟩⟩,
     ⟨5, ⟨⟨115,159,35,1187⟩,0xb24d00000,18685854⟩, ⟨⟨521,724,153,17608⟩,0x3d118e80000,0x1bd78704c⟩⟩,
     ⟨6, ⟨⟨114,158,34,1481⟩,0xab2c00000,17916156⟩, ⟨⟨585,813,172,18018⟩,0x56714d40000,0x2c405b86b⟩⟩,
     ⟨10, ⟨⟨142,197,43,1768⟩,0x14bde80000,43318982⟩, ⟨⟨666,926,195,23938⟩,0x7f04c380000,0x4a1c95ad2⟩⟩,
     ⟨16, ⟨⟨195,270,60,1985⟩,0x35dfb80000,0x921d91e⟩, ⟨⟨869,1208,255,30502⟩,0x11a29c000000,0xd6957b128⟩⟩,
     ⟨18, ⟨⟨236,327,73,1859⟩,0x5f7bb40000,0x139cbdb4⟩, ⟨⟨1028,1429,302,30599⟩,0x1d31d5640000,0x1a41f86f48⟩⟩,
     ⟨24, ⟨⟨234,324,73,2988⟩,0x5daf840000,0x130a6f27⟩, ⟨⟨1267,1761,373,36637⟩,0x36b2a6f80000,0x3c9863ad3c⟩⟩,
     ⟨32, ⟨⟨261,362,81,5153⟩,0x813b280000,0x1d6fb003⟩, ⟨⟨1466,2038,431,46668⟩,0x54997c200000,0x6c7e6759da⟩⟩,
     ⟨36, ⟨⟨250,347,75,47631⟩,0x6ece680000,0x18392b4c⟩, ⟨⟨1215,1689,356,84012⟩,0x3011c0200000,0x33175ef1d6⟩⟩,
     ⟨54, ⟨⟨444,615,137,5303⟩,0x274cf340000,0xf2191e37⟩, ⟨⟨2194,3050,645,71333⟩,0x11b429fac0000,0x21f78372cbf⟩⟩,
     ⟨81, ⟨⟨680,942,212,6492⟩,0x8dc48280000,0x538e63a35⟩, ⟨⟨3385,4705,995,96391⟩,0x40f5ebab00000,0xc029d47a706⟩⟩,
     ⟨135, ⟨⟨998,1383,310,11820⟩,0x1bdf3ba00000,0x181eba870b⟩, ⟨⟨5282,7341,1556,154211⟩,0xf7195a1840000,0x4741ba66013a⟩⟩]
  | .h2294 =>
    [⟨0, ⟨⟨73,101,22,878⟩,0x2e5640000,3108650⟩, ⟨⟨352,489,103,10763⟩,0x12dda700000,0x5cfd94a5⟩⟩,
     ⟨1, ⟨⟨78,108,24,1006⟩,0x392740000,4103823⟩, ⟨⟨345,480,101,13083⟩,0x11c61f80000,0x564a51c0⟩⟩,
     ⟨2, ⟨⟨86,119,26,1061⟩,0x4b3780000,5931589⟩, ⟨⟨385,535,112,13830⟩,0x188bf840000,0x84679137⟩⟩,
     ⟨3, ⟨⟨94,130,29,1105⟩,0x633bc0000,8531244⟩, ⟨⟨411,572,120,15084⟩,0x1dec1a80000,0xad1e0c80⟩⟩,
     ⟨4, ⟨⟨102,141,31,1166⟩,0x7cec00000,11621252⟩, ⟨⟨438,609,128,16326⟩,0x2436d340000,0xde912dc3⟩⟩,
     ⟨5, ⟨⟨108,150,33,1260⟩,0x948040000,14840297⟩, ⟨⟨522,726,153,15779⟩,0x3d548e40000,0x1c16ef1c7⟩⟩,
     ⟨6, ⟨⟨108,149,33,1589⟩,0x948040000,14526868⟩, ⟨⟨570,792,167,16543⟩,0x4fc3e700000,0x27c2e15db⟩⟩,
     ⟨10, ⟨⟨142,197,43,1679⟩,0x14bde80000,43318982⟩, ⟨⟨696,968,204,20721⟩,0x910a3980000,0x5884788a7⟩⟩,
     ⟨16, ⟨⟨163,226,50,3079⟩,0x1f8a780000,75401397⟩, ⟨⟨851,1183,249,27859⟩,0x108708880000,0xc4f2a7606⟩⟩,
     ⟨18, ⟨⟨221,306,68,1918⟩,0x4e346c0000,0xf032b8c⟩, ⟨⟨952,1324,279,29044⟩,0x17270e900000,0x1350bb1fb5⟩⟩,
     ⟨24, ⟨⟨212,294,65,3972⟩,0x44e9c40000,0xcc1a54f⟩, ⟨⟨1115,1550,329,35921⟩,0x255cff880000,0x2473d5ffe4⟩⟩,
     ⟨32, ⟨⟨261,362,82,4794⟩,0x826c0c0000,0x1db6eefa⟩, ⟨⟨1463,2034,430,42399⟩,0x54106e900000,0x6b9d823520⟩⟩,
     ⟨36, ⟨⟨246,341,75,46786⟩,0x6ae4280000,0x16e7d3b2⟩, ⟨⟨1220,1696,357,67968⟩,0x309db61c0000,0x33e3754396⟩⟩,
     ⟨42, ⟨⟨279,386,85,43857⟩,0x9b80980000,0x25892b87⟩, ⟨⟨1240,1725,359,125646⟩,0x32a0cb700000,0x370899d961⟩⟩,
     ⟨54, ⟨⟨534,740,167,4011⟩,0x44f1df00000,0x1ff6e1863⟩, ⟨⟨2252,3131,661,63840⟩,0x131ef423c0000,0x25ab1ba8825⟩⟩,
     ⟨81, ⟨⟨637,883,197,7007⟩,0x73e2ad80000,0x401d0f0c6⟩, ⟨⟨3474,4830,1019,88004⟩,0x461aa92080000,0xd5013df2ef9⟩⟩,
     ⟨100, ⟨⟨774,1072,239,8364⟩,0xcf60ca00000,0x8af950b98⟩, ⟨⟨4170,5798,1223,106403⟩,0x7934721300000,0x1ba1a89b2ba1⟩⟩,
     ⟨135, ⟨⟨1042,1443,329,10486⟩,0x201c60040000,0x1cf53a5560⟩, ⟨⟨5487,7630,1607,140227⟩,0x113c22e7a00000,0x52bdbe618ec3⟩⟩]
  | .h7773 =>
    [⟨0, ⟨⟨11,15,3,125⟩,55574528,2194⟩, ⟨⟨20,28,4,256⟩,0xdc00000,17031⟩⟩,
     ⟨2, ⟨⟨21,29,6,151⟩,0x13cc0000,24733⟩, ⟨⟨38,53,9,375⟩,0x5d840000,211909⟩⟩,
     ⟨5, ⟨⟨34,47,10,230⟩,0x4f100000,156979⟩, ⟨⟨64,89,15,587⟩,0x1a3600000,1564938⟩⟩,
     ⟨10, ⟨⟨54,75,16,378⟩,0x12f140000,957077⟩, ⟨⟨101,141,24,985⟩,0x64f3c0000,9562298⟩⟩]
end P3_7
end
section
namespace P3_7
open P3 (HighBand agreement p blockLength)
abbrev degreeAt := P1_7.degreeAt
abbrev quotientOrder := P1_7.quotientOrder
def gap (hi : ℕ) := agreement - degreeAt hi
def scale (hi : ℕ) := agreement * gap hi
def muNum (hi : ℕ) := agreement * (blockLength - degreeAt hi)
def lambdaNum (hi : ℕ) := blockLength * gap hi
abbrev ceilRatio := P1_7.ceilRatio
abbrev singularDegree := P1_7.singularDegree
abbrev singularFee := P1_7.singularFee
def persistentFee (lo hi e v : ℕ) : ℕ :=
  let t := lambdaNum hi * quotientOrder lo
  let a := muNum hi + 2 * t * (e - 1)
  let b := 2 * hi * muNum hi + 2 * t * v
  ceilRatio (e * b^2 + 2 * v * a * b) ((scale hi)^2) + e
def properFee (lo hi e v : ℕ) : ℕ :=
  let bc := quotientOrder lo + 1
  let ac := 1 + bc * (e - 1)
  let cc := bc * v + 2 * hi
  let bn := lambdaNum hi * quotientOrder lo
  let an := muNum hi + bn * (e - 1)
  let cn := bn * v + 2 * hi * muNum hi
  ceilRatio (e * cc * cn +
    v * (cn * ((2*e-2)*bc + ac) + cc * ((2*e-2)*bn + an)) +
    v^2 * ((ac - 2*bc) * bn + an * bc)) (scale hi)
def flatFee (hi v : ℕ) : ℕ := ceilRatio (P3.t * (p+1) * v) (gap hi)
def tangentFee (lo hi e v : ℕ) : ℕ := properFee lo hi e v + flatFee hi v + e
def wholePrice (lo hi e v : ℕ) : ℕ :=
  if v = 0 then e else singularFee e v +
    if e ≤ 2 then persistentFee lo hi e v else tangentFee lo hi e v
structure GradeOK (lo hi fullU cap e : ℕ) (g : Grade) : Prop where
  sub : g.slots ≤ fullU
  separant : singularDegree e g.seedCap < p
  flat : e * degreeAt hi + g.seedCap < p
  fee : wholePrice lo hi e g.seedCap ≤ cap
theorem grade_of_literals {lo hi fullU cap e v U D m price : ℕ}
    (hU : U ≤ fullU) (hD : singularDegree e v = D) (hDp : D < p)
    (hm : e * degreeAt hi + v = m) (hmp : m < p)
    (hprice : wholePrice lo hi e v = price) (hle : price ≤ cap) :
    GradeOK lo hi fullU cap e ⟨v,U⟩ :=
  ⟨hU, hD.le.trans_lt hDp, hm.le.trans_lt hmp, hprice.le.trans hle⟩
end P3_7
end
section
namespace P3_7
open P3 (K HighBand)
abbrev PrefixFees := P1_7.PrefixFees
def fees : HighBand → PrefixFees
  | .h2274 => ⟨0xc904390c91470f, 0x17d3980110, 0x2ff61282b53d4, 0x509cd82b45d562, 0x198fe0fe4a37, 0x77b6ff61e2a14⟩
  | .h2294 => ⟨0xb8a9a55071628c, 0x19d622fd92, 0x2e2cc452ad45f, 0x4de68be1bd94f6, 0x241721d0f19c, 0x94c0f66257b34⟩
  | .h7773 => ⟨0x25f3ecf8e7b30, 15469025, 0xe395400f361, 0x766d97f5fb4, 0x28950a2d5, 0x7d0bf001f82⟩
structure PrefixBooks (b : HighBand) where
  loss : Finset K
  point : Finset K
  lowSeed : Finset K
  lowJet : Finset K
  fixedODE : Finset K
  content : Finset K
  loss_le : loss.card ≤ (fees b).loss
  point_le : point.card ≤ (fees b).point
  lowSeed_le : lowSeed.card ≤ (fees b).lowSeed
  lowJet_le : lowJet.card ≤ (fees b).lowJet
  fixedODE_le : fixedODE.card ≤ (fees b).fixedODE
  content_le : content.card ≤ (fees b).content
noncomputable def PrefixBooks.union {b} (B : PrefixBooks b) : Finset K := by
  classical exact B.loss ∪ B.point ∪ B.lowSeed ∪ B.lowJet ∪ B.fixedODE ∪ B.content
end P3_7
end
section
namespace P3_7
noncomputable section
open Polynomial
open P3 (HighBand AnchorModel AnchoredFamily K p node twist agreement)
open K1_14 (L FX Seeds Equation Shape Jet Banks SeedBound liftPoly graphEval atX atMark
  jetAt triangle slots shapeSum)
open K1_14_3 (Surface Parent)
open scoped BigOperators
def asP1Model {u del} (M : AnchorModel u del) : P1.AnchorModel u del :=
  { M with height_bound := M.height_bound.trans (by decide : P3.heightCap ≤ P1.heightCap) }
def fullCutoff (s : Shape) := s.m * agreement - 1
def buffered (h r : ℕ) (s : Shape) := fullCutoff s - 2*h*r
abbrev debit := P1_7.debit
structure BufferedPair (h : ℕ) (rows : Banks) (s : Stage) where
  free : Jet
  moving : Jet
  free_ne : free ≠ 0
  moving_ne : moving ≠ 0
  free_mem : free ∈ rows s.free.shape (buffered h s.reserve s.free.shape)
  moving_mem : moving ∈ rows s.moving.shape (buffered h s.reserve s.moving.shape)
  no_moving : K1_14_3.NoMovingCommon free moving
abbrev Pairs (b : HighBand) (h : ℕ) (rows : Banks) :=
  ∀ s ∈ stages b, BufferedPair h rows s
def BankPass (rows : Banks) (s : Shape) (q : Surface) : Prop :=
  ∀ P ∈ rows s (fullCutoff s), P ∈ q.asIdeal
def PairPass {h rows s} (pair : BufferedPair h rows s) (q : Surface) : Prop :=
  BankPass rows s.free.shape q ∧ BankPass rows s.moving.shape q ∧
    K1_14_3R.compatible pair.free pair.moving q
def MarkOn {u del} (M : AnchorModel u del) {Γ} (F : AnchoredFamily M Γ)
    (q : Surface) (γ : K) : Prop :=
  q.asIdeal ≤ RingHom.ker
    (eval₂RingHom (eval₂RingHom (graphEval (M.label γ)) (atX (F.scalar γ)))
      (atX (F.scalar γ).derivative))
structure PrefixInventory (b : HighBand) {u del} (M : AnchorModel u del) {Γ}
    (F : AnchoredFamily M Γ) {rows : Banks} (pairs : Pairs b M.overhead.toNat rows) where
  books : PrefixBooks b
  parents : Finset Surface
  geometric : ∀ q ∈ parents, Parent q
  stage_pass : ∀ q ∈ parents, ∀ s (hs : s ∈ stages b), 0 < s.reserve →
    PairPass (pairs s hs) q
  terminal_pass : ∀ q ∈ parents, BankPass rows (terminal b).shape q
  covers : ∀ γ ∈ Γ, γ ∈ books.union ∨ ∃ q ∈ parents, MarkOn M F q γ
def curveUnit (hi g : ℕ) : ℚ :=
  let d := degreeAt hi
  (2*(g : ℚ)-1) * (1 + 2*((P3.blockLength : ℚ)/agreement)*d) +
    ((P3.blockLength - d : ℕ) : ℚ) / gap hi
def jointGain (h : ℕ) (s : Shape) (E v : ℕ) : ℕ :=
  shapeSum s fun q j =>
    let g := (q-j)/E
    let x := s.m*agreement+j - q*(131071-h)
    let c := fun a => slots s.U (a*v)
    (∑ a ∈ Finset.range g, (c a - c (a+1)) * (x - 2*h*(j+a))) +
      c g * (x - 2*h*(j+g))
end
end P3_7
end
section
namespace P3_7
open P3 (HighBand agreement p)
local notation "r!" x "," y "," z => grade_of_literals (D := x) (m := y) (price := z)
  (by decide) rfl (by decide) rfl (by decide) rfl (by decide)
private theorem guard {lo hi m B top edge : ℕ}
    (hl : 0 < lo) (hh : hi ≤ 33249) (ht : m*agreement = top) (hp : 0 < top)
    (hc : top < p) (hw : B*(131071-lo) = edge) (he : edge ≤ top) :
    0 < lo ∧ hi ≤ 33249 ∧ 0 < m*agreement ∧ m*agreement < p ∧ B*(131071-lo) ≤ m*agreement :=
  ⟨hl, hh, ht.symm ▸ hp, ht.symm ▸ hc, hw.le.trans (he.trans ht.ge)⟩
local notation "g!" t "," w => guard (top := t) (edge := w) (by decide) (by decide) rfl
  (by decide) (by decide) rfl (by decide)
end P3_7
end
section
namespace P3_7
noncomputable section
open P3 (K I node p agreement blockLength AnchorModel AnchoredFamily)
open K1_14_2_4 (taylorPower ordinateBound)
open P1_7_3 (persistentNodes hits_persistent section_bounds regular_chart persistent_taylor)
open Finset Polynomial ProximityPrize.Benchmark
end
end P3_7
end
section
namespace P3_7
noncomputable section
open Polynomial
open P3 (HighBand AnchorModel AnchoredFamily agreement p)
open K1_14 (Banks Jet Equation SeedBound)
open K1_14_3 (Surface Parent ProjectedProduct OrderAt)
open K1_14_4 (seedDegree seedDegree_le_iff)
end
end P3_7
end
