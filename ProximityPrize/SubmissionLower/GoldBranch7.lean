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
def subbank (b : HighBand) (g : Grade) : Bank :=
  let t := terminal b
  { t with shape := { t.shape with U := g.slots } }
def grades : HighBand → List Grade
  | .h2274 =>
    [⟨358,162873⟩,⟨353,164297⟩,⟨348,166033⟩,⟨342,167408⟩,
     ⟨336,169216⟩,⟨330,171591⟩,⟨323,173880⟩,⟨316,177154⟩,
     ⟨308,180959⟩,⟨300,187112⟩,⟨290,195637⟩,⟨277,211000⟩,
     ⟨262,211000⟩,⟨244,211000⟩,⟨225,211000⟩,⟨202,211000⟩,
     ⟨177,211000⟩,⟨150,211000⟩,⟨121,211000⟩,⟨89,211000⟩,
     ⟨55,211000⟩,⟨19,211000⟩]
  | .h2294 =>
    [⟨330,179424⟩,⟨325,180915⟩,⟨320,182775⟩,⟨315,185099⟩,
     ⟨309,187083⟩,⟨303,189769⟩,⟨296,192397⟩,⟨289,196316⟩,
     ⟨281,201102⟩,⟨273,209391⟩,⟨262,221352⟩,⟨249,234728⟩,
     ⟨233,234728⟩,⟨214,234728⟩,⟨193,234728⟩,⟨170,234728⟩,
     ⟨144,234728⟩,⟨116,234728⟩,⟨85,234728⟩,⟨52,234728⟩,
     ⟨17,234728⟩]
  | .h7773 =>
    [⟨25,886⟩,⟨23,913⟩,⟨21,946⟩,⟨18,946⟩,
     ⟨13,946⟩,⟨7,946⟩]
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
def AllGrades (lo hi fullU cap : ℕ) : ℕ → List Grade → Prop
  | _, [] => True
  | e, g :: gs => GradeOK lo hi fullU cap e g ∧ AllGrades lo hi fullU cap (e+1) gs
theorem get_grade {lo hi fullU cap : ℕ} (gs : List Grade) (e : ℕ)
    (hall : AllGrades lo hi fullU cap e gs) (i : Fin gs.length) :
    GradeOK lo hi fullU cap (i.val + e) (gs.get i) := by
  induction gs generalizing e with
  | nil => exact Fin.elim0 i
  | cons g gs ih =>
    rcases i with ⟨_ | j, hj⟩
    · change GradeOK lo hi fullU cap (0+e) g
      simpa only [Nat.zero_add] using hall.1
    · have h := ih (e+1) hall.2 ⟨j, by simpa using hj⟩
      simpa only [List.get_cons_succ, Nat.succ_add, Nat.add_succ] using h
theorem grade_of_literals {lo hi fullU cap e v U D m price : ℕ}
    (hU : U ≤ fullU) (hD : singularDegree e v = D) (hDp : D < p)
    (hm : e * degreeAt hi + v = m) (hmp : m < p)
    (hprice : wholePrice lo hi e v = price) (hle : price ≤ cap) :
    GradeOK lo hi fullU cap e ⟨v,U⟩ :=
  ⟨hU, hD.le.trans_lt hDp, hm.le.trans_lt hmp, hprice.le.trans hle⟩
theorem sheets_le_price (lo hi e v : ℕ) : e ≤ wholePrice lo hi e v := by
  unfold wholePrice
  split
  · exact le_rfl
  · split
    · dsimp only [persistentFee]
      omega
    · unfold tangentFee
      omega
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
theorem fees_total (b : HighBand) :
    (fees b).loss + (fees b).point + (fees b).lowSeed + (fees b).lowJet +
      (fees b).fixedODE + (fees b).content = b.row.prefixFee := by
  cases b <;> rfl
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
private theorem union_le {A B : Finset K} {a b : ℕ} (ha : A.card ≤ a) (hb : B.card ≤ b) :
    (A ∪ B).card ≤ a+b := (Finset.card_union_le _ _).trans (Nat.add_le_add ha hb)
theorem PrefixBooks.card_union {b} (B : PrefixBooks b) : B.union.card ≤ b.row.prefixFee := by
  rw [← fees_total b]
  exact union_le (union_le (union_le (union_le (union_le B.loss_le B.point_le)
    B.lowSeed_le) B.lowJet_le) B.fixedODE_le) B.content_le
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
def InBand (b : HighBand) (w : ℤ) : Prop := (b.row.lo : ℤ) ≤ w ∧ w ≤ (b.row.hi : ℤ)
def asP1Model {u del} (M : AnchorModel u del) : P1.AnchorModel u del :=
  { M with height_bound := M.height_bound.trans (by decide : P3.heightCap ≤ P1.heightCap) }
def asP1Family {u del} (M : AnchorModel u del) {Γ} (F : AnchoredFamily M Γ) :
    P1.AnchoredFamily (asP1Model M) Γ where
  scalar := F.scalar
  distinct := F.distinct
  mark γ hγ := by
    let m := F.mark γ hγ
    let B : P1.BadMark u γ :=
      { m.bad with agreement := (by decide : P1.agreement ≤ P3.agreement).trans m.bad.agreement }
    exact ⟨B, m.avoids_deleted, m.scalar_fixed, m.scalar_degree, m.scalar_hits, m.pole_unit, m.identity⟩
abbrev AdjacentChart {u del} (M : AnchorModel u del) {Γ} (F : AnchoredFamily M Γ) :=
  P1_7.AdjacentChart (asP1Model M) (asP1Family M F)
abbrev GradeIndex (b : HighBand) := Fin (grades b).length
def Listed (b : HighBand) (t : Bank) : Prop :=
  t = terminal b ∨ (∃ s ∈ stages b, t = s.free ∨ t = s.moving) ∨
    ∃ i : GradeIndex b, t = subbank b ((grades b).get i)
def fullCutoff (s : Shape) := s.m * agreement - 1
def buffered (h r : ℕ) (s : Shape) := fullCutoff s - 2*h*r
abbrev debit := P1_7.debit
def RankFloor (h : ℕ) (t : Bank) (rows : Banks) : Prop :=
  ∀ W < t.shape.m * agreement,
    (∀ q ≤ t.shape.B, ∀ j ≤ min q t.shape.J, q * (131071-h) ≤ W+1+j) →
    triangle t.shape.U * shapeSum t.shape (fun q j => W+1+j - q*(131071-h)) ≤
      debit h t + ∑ w ∈ Finset.range (W+1), Module.finrank FX (rows t.shape w)
structure Source (b : HighBand) {u del} (M : AnchorModel u del) {Γ}
    (F : AnchoredFamily M Γ) (rows : Banks) : Prop where
  nested : ∀ t, Listed b t → ∀ t', Listed b t' →
    t.shape.m = t'.shape.m → t.shape.B = t'.shape.B → t.shape.J = t'.shape.J →
    t.shape.U ≤ t'.shape.U → ∀ W W', W ≤ W' → rows t.shape W ≤ rows t'.shape W'
  necessary : ∀ t, Listed b t → ∀ W < t.shape.m * agreement, ∀ P ∈ rows t.shape W,
    ∀ γ ∈ Γ, jetAt P (M.label γ) (F.scalar γ) = 0
  shape : ∀ t, Listed b t → ∀ W, ∀ P ∈ rows t.shape W, K1_14_3.RowCaps P t.shape
  leading : ∀ t, Listed b t → K1_14_3.LeadingFilter M.overhead.toNat rows t.shape
  shift : ∀ t, Listed b t → K1_14_3.SeedShift M.overhead.toNat rows t.shape
  floor_bound : ∀ t, Listed b t → RankFloor M.overhead.toNat t rows
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
def CurveTariff (b : HighBand) {u del} (M : AnchorModel u del) {Γ}
    (F : AnchoredFamily M Γ) : Prop :=
  ∀ T ⊆ Γ, ∀ J g H, 0 < g → g ≤ 80 →
    K1_14_2.SmallRootCurve J g H →
    Module.finrank K1_14_2.SeedField (K1_14_2.RootSeedSection J) < p →
    (∀ γ ∈ T, K1_14_2.OnRoot J (M.label γ) (F.scalar γ)) →
    (T.card : ℚ) ≤ curveUnit b.row.hi g * H + g
abbrev Test (b : HighBand) := Option (GradeIndex b)
def tested (b : HighBand) : Test b → Bank
  | none => terminal b
  | some i => subbank b ((grades b).get i)
def threshold (b : HighBand) : Test b → ℕ
  | none => (grades b).length + 1
  | some i => i.val + 1
def seedThreshold (b : HighBand) : Test b → ℕ
  | none => 0
  | some i => ((grades b).get i).seedCap + 1
def contactPower (h : ℕ) (s : Shape) (W : ℕ) := 1 + (fullCutoff s - W)/(2*h)
def jointGain (h : ℕ) (s : Shape) (E v : ℕ) : ℕ :=
  shapeSum s fun q j =>
    let g := (q-j)/E
    let x := s.m*agreement+j - q*(131071-h)
    let c := fun a => slots s.U (a*v)
    (∑ a ∈ Finset.range g, (c a - c (a+1)) * (x - 2*h*(j+a))) +
      c g * (x - 2*h*(j+g))
structure TerminalTrace (h : ℕ) (t : Bank) (rows : Banks) (f : Equation) : Prop where
  floor_bound : RankFloor h t rows
  shape : ∀ W, ∀ P ∈ rows t.shape W, K1_14_3.RowCaps P t.shape
  leading : K1_14_3.LeadingFilter h rows t.shape
  divides : ∀ W < t.shape.m * agreement, ∀ P ∈ rows t.shape W, P ≠ 0 →
    f ^ (contactPower h t.shape W - P.natDegree) ∣ P.leadingCoeff
abbrev Reduced := P1_7.Reduced
abbrev regularRoot := P1_7.regularRoot
def RegularCount {u del} (M : AnchorModel u del) {Γ}
    (F : AnchoredFamily M Γ) (f : Equation) (fee : ℕ) : Prop :=
  ∀ T ⊆ Γ, (∀ γ ∈ T, regularRoot f (M.label γ) (F.scalar γ)) → T.card ≤ fee
end
end P3_7
end
section
namespace P3_7
open P3 (HighBand agreement p)
local notation "r!" x "," y "," z => grade_of_literals (D := x) (m := y) (price := z)
  (by decide) rfl (by decide) rfl (by decide) rfl (by decide)
private theorem r2274 : AllGrades 2274 2293 211000 0x2859f4cc0c22fa4 1 (grades .h2274) :=
  ⟨r! 358,133722,0x401bfd8f925c68,
   r! 1059,267081,0xf94ecb069f978c,
   r! 1740,400440,0xb0c4a46173028a,
   r! 2394,533798,0x1051a8c7f0f8575,
   r! 3024,667156,0x153421eb7d77d96,
   r! 3630,800514,0x19b661313870eb4,
   r! 4199,933871,0x1dabf828fb11146,
   r! 4740,1067228,0x2138e3f0e629122,
   r! 5236,1200584,0x24249ab831b95a7,
   r! 5700,1333940,0x26a2f58cce21b7d,
   r! 6090,1467294,0x282a673e56f963d,
   r! 6371,1600645,0x2859f4cc0c22fa4,
   r! 6550,1733994,0x276a5189432368d,
   r! 6588,1867340,0x250fc4befc2519f,
   r! 6525,2000685,0x21f5d588977674d,
   r! 6262,2134026,0x1d580cb8e921c2f,
   r! 5841,2267365,0x180b5d6631aef26,
   r! 5250,2400702,0x125b3bb1780ce93,
   r! 4477,2534037,0xca73f883290e90,
   r! 3471,2667369,0x73ad140540e4b2,
   r! 2255,2800699,0x2e896c75c2103c,
   r! 817,2934027,0x5d8b0cdc0fb02, trivial⟩
private theorem r2294 : AllGrades 2294 7772 234728 0x20ca3b555c8e27a 1 (grades .h2294) :=
  ⟨r! 330,139173,0x367cbf2b3c8f8b,
   r! 975,278011,0xd35a16fd8c6626,
   r! 1600,416849,0x957d85f55ee43f,
   r! 2205,555687,0xdd88b17f3763fc,
   r! 2781,694524,0x11ef6625b93031b,
   r! 3333,833361,0x15ae0c5dc88f110,
   r! 3848,972197,0x18ebfe746ef65f0,
   r! 4335,1111033,0x1bca9ff4cc37a6b,
   r! 4777,1249868,0x1e16ac0e92f3f25,
   r! 5187,1388703,0x20000c144f6ed8e,
   r! 5502,1527535,0x20ca3b555c8e27a,
   r! 5727,1666365,0x209ce1cacb593fb,
   r! 5825,1805192,0x1f2e2ad5dee3546,
   r! 5778,1944016,0x1c844ebede72c3b,
   r! 5597,2082838,0x18ff22328e24508,
   r! 5270,2221658,0x14cafe3c8f31401,
   r! 4752,2360475,0xfec9f7e28079b1,
   r! 4060,2499290,0xafcc740ec78971,
   r! 3145,2638102,0x640a5df52871c9,
   r! 2028,2776912,0x2796d12bec1dba,
   r! 697,2915720,0x47d045494f40b, trivial⟩
private theorem r7773 : AllGrades 7773 33249 946 0x10b6e3d18a24d 1 (grades .h7773) :=
  ⟨r! 25,164345,0x5051b7d1b4d8,
   r! 69,328663,0x10b6e3d18a24d,
   r! 105,492981,0xa25355e2c46b,
   r! 126,657298,0xb79d0bdf8483,
   r! 117,821613,0x844bd62a1564,
   r! 77,985927,0x343b7c669744, trivial⟩
theorem grades_checked (b : HighBand) :
    AllGrades b.row.lo b.row.hi (terminal b).shape.U b.row.retained 1 (grades b) := by
  cases b with
  | h2274 => exact r2274
  | h2294 => exact r2294
  | h7773 => exact r7773
theorem grade_checked (b : HighBand) (i : Fin (grades b).length) :
    GradeOK b.row.lo b.row.hi (terminal b).shape.U b.row.retained (i.val+1) ((grades b).get i) :=
  get_grade _ _ (grades_checked b) i
private theorem guard {lo hi m B top edge : ℕ}
    (hl : 0 < lo) (hh : hi ≤ 33249) (ht : m*agreement = top) (hp : 0 < top)
    (hc : top < p) (hw : B*(131071-lo) = edge) (he : edge ≤ top) :
    0 < lo ∧ hi ≤ 33249 ∧ 0 < m*agreement ∧ m*agreement < p ∧ B*(131071-lo) ≤ m*agreement :=
  ⟨hl, hh, ht.symm ▸ hp, ht.symm ▸ hc, hw.le.trans (he.trans ht.ge)⟩
local notation "g!" t "," w => guard (top := t) (edge := w) (by decide) (by decide) rfl
  (by decide) (by decide) rfl (by decide)
theorem terminal_guards (b : HighBand) :
    0 < b.row.lo ∧ b.row.hi ≤ 33249 ∧ 0 < (terminal b).shape.m * agreement ∧
    (terminal b).shape.m * agreement < p ∧
    (terminal b).shape.B * (131071-b.row.lo) ≤ (terminal b).shape.m*agreement := by
  cases b with
  | h2274 => exact g! 0x46cdbab8,0x46699b04
  | h2294 => exact g! 0x50febc62,0x50a4175a
  | h7773 => exact g! 22317892,21330554
end P3_7
end
section
namespace P3_7
noncomputable section
open P3 (K I node p agreement blockLength AnchorModel AnchoredFamily)
open K1_14_2_4 (taylorPower ordinateBound)
open P1_7_3 (persistentNodes hits_persistent section_bounds regular_chart persistent_taylor)
open Finset Polynomial ProximityPrize.Benchmark
structure FixedWord (w : I → K) (U : Finset K) (s : K → K[X]) (d : ℕ) : Prop where
  distinct : Set.InjOn s (U : Set K)
  degree : ∀ γ ∈ U, (s γ).natDegree ≤ d
  hits : ∀ γ ∈ U, ∃ B : Finset I, agreement ≤ B.card ∧ ∀ i ∈ B, (s γ).eval (node i) = w i
theorem persistent_card_le {w U s d} (hw : FixedWord w U s d) (hU : 1 < U.card) :
    (persistentNodes w U s).card ≤ d := by
  obtain ⟨a, ha, b, hb, hab⟩ := one_lt_card.mp hU
  let P := s a - s b
  have hp : P ≠ 0 := sub_ne_zero.mpr fun eq => hab (hw.distinct ha hb eq)
  refine (FrobeniusLocator.Strata.root_nodes_card_le node IRSProfile.domain.injective P hp _ ?_).trans
    ((natDegree_sub_le _ _).trans (max_le (hw.degree a ha) (hw.degree b hb)))
  intro i hi
  change ((s a) - (s b)).eval (node i) = 0
  rw [Polynomial.eval_sub, hits_persistent ha hi, hits_persistent hb hi, sub_self]
theorem section_incidence {w U s d} (hw : FixedWord w U s d) (D : ℕ)
    (hsection : ∀ i : I, (∃ γ ∈ U, (s γ).eval (node i) ≠ w i) →
      (U.filter fun γ => (s γ).eval (node i) = w i).card ≤ D) :
    (agreement - (persistentNodes w U s).card) * U.card ≤
      (blockLength - (persistentNodes w U s).card) * D := by
  classical
  let sites := persistentNodes w U s
  let nodes : Finset I := univ \ sites
  let hits (γ : K) := nodes.filter fun i => (s γ).eval (node i) = w i
  let occ (i : I) := U.filter fun γ => (s γ).eval (node i) = w i
  have hhit (γ : K) (hγ : γ ∈ U) : agreement - sites.card ≤ (hits γ).card := by
    obtain ⟨B, hB, hvals⟩ := hw.hits γ hγ
    let good : Finset I := univ.filter fun i => (s γ).eval (node i) = w i
    have hgood : agreement ≤ good.card :=
      hB.trans (card_le_card fun i hi => mem_filter.mpr ⟨mem_univ _, hvals i hi⟩)
    have hZG : sites ⊆ good := fun i hi => mem_filter.mpr ⟨mem_univ _, hits_persistent hγ hi⟩
    have heq : hits γ = good \ sites := by
      ext i
      simp only [hits, nodes, good, mem_filter, mem_sdiff, mem_univ, true_and]
      exact and_comm
    rw [heq, card_sdiff_of_subset hZG]
    exact Nat.sub_le_sub_right hgood _
  have hnodes : nodes.card = blockLength - sites.card := by
    rw [card_sdiff_of_subset (subset_univ sites), card_univ, IRSProfile.card_index]
  calc
    _ = ∑ γ ∈ U, (agreement - sites.card) := by rw [sum_const, smul_eq_mul, Nat.mul_comm]
    _ ≤ ∑ γ ∈ U, (hits γ).card := sum_le_sum hhit
    _ = ∑ i ∈ nodes, (occ i).card := by simp only [hits, occ, card_filter]; rw [sum_comm]
    _ ≤ ∑ _i ∈ nodes, D := by
      apply sum_le_sum
      intro i hi
      apply hsection i
      by_contra! h
      exact (mem_sdiff.mp hi).2 (mem_filter.mpr ⟨mem_univ _, h⟩)
    _ = _ := by rw [sum_const, smul_eq_mul, hnodes]
private def rho (s : ℕ) : ℚ :=
  ((blockLength - s : ℕ) : ℚ) / ((agreement - s : ℕ) : ℚ)
private abbrev density : ℚ := (blockLength : ℚ) / agreement
private theorem weights {s d : ℕ} (hs : s ≤ d) (hd : d < agreement)
    (haux : rho d ≤ density * d) :
    rho s ≤ rho d ∧ rho s * (max 1 (d-s) : ℕ) ≤ density * d := by
  have hAN : agreement ≤ blockLength := by decide
  have hsA := hs.trans_lt hd
  have hdN := hd.le.trans hAN
  have hsN := hs.trans hdN
  have hAs : (0 : ℚ) < (agreement : ℚ) - s := sub_pos.mpr (by exact_mod_cast hsA)
  have hAd : (0 : ℚ) < (agreement : ℚ) - d := sub_pos.mpr (by exact_mod_cast hd)
  have hmain : rho s ≤ rho d := by
    unfold rho
    rw [Nat.cast_sub hsN, Nat.cast_sub hsA.le, Nat.cast_sub hdN, Nat.cast_sub hd.le]
    apply (div_le_div_iff₀ hAs hAd).mpr
    have h := mul_nonneg (sub_nonneg.mpr (show (s : ℚ) ≤ d by exact_mod_cast hs))
      (sub_nonneg.mpr (show (agreement : ℚ) ≤ blockLength by exact_mod_cast hAN))
    nlinarith only [h]
  refine ⟨hmain, ?_⟩
  by_cases heq : s = d
  · subst s
    simpa using haux
  have hpos : 1 ≤ d - s := by omega
  rw [max_eq_right hpos]
  have hden : (0 : ℚ) < (agreement : ℚ) := by exact_mod_cast (by decide : 0 < agreement)
  have hfrac : ((d-s : ℕ) : ℚ) / ((agreement-s : ℕ) : ℚ) ≤ (d : ℚ) / agreement := by
    rw [Nat.cast_sub hs, Nat.cast_sub hsA.le]
    apply (div_le_div_iff₀ hAs hden).mpr
    have h := mul_nonneg (Nat.cast_nonneg s : (0 : ℚ) ≤ s) hAd.le
    nlinarith only [h]
  calc
    _ = ((blockLength-s : ℕ) : ℚ) * (((d-s : ℕ) : ℚ) / ((agreement-s : ℕ) : ℚ)) := by
      unfold rho
      ring
    _ ≤ (blockLength : ℚ) * ((d : ℚ) / agreement) :=
      mul_le_mul (by exact_mod_cast Nat.sub_le blockLength s) hfrac (by positivity) (by positivity)
    _ = density * d := by ring
private theorem rho_at_endpoint {d : ℕ} (hl : 131071 ≤ d) (hh : d ≤ 164320) :
    rho d ≤ density * d := by
  have hdA : d < agreement := hh.trans_lt (by decide)
  have hdN : d ≤ blockLength := hh.trans (by decide)
  have hrho : rho d ≤ 17 := by
    unfold rho
    have hp : (0 : ℚ) < ((agreement - d : ℕ) : ℚ) := by exact_mod_cast Nat.sub_pos_of_lt hdA
    apply (div_le_iff₀ hp).mpr
    rw [Nat.cast_sub hdN, Nat.cast_sub hdA.le]
    change (262144 : ℚ) - d ≤ 17 * ((179983 : ℚ) - d)
    have hQ : (d : ℚ) ≤ 164320 := by exact_mod_cast hh
    linarith only [hQ]
  have hDensity : 1 ≤ density := by
    apply (le_div_iff₀ (show (0 : ℚ) < (agreement : ℚ) by positivity)).mpr
    rw [one_mul]
    exact_mod_cast (by decide : agreement ≤ blockLength)
  exact hrho.trans (calc
    (17 : ℚ) ≤ (d : ℚ) := by exact_mod_cast (show 17 ≤ d by omega)
    _ = 1 * (d : ℚ) := (one_mul _).symm
    _ ≤ density * d := mul_le_mul_of_nonneg_right hDensity (Nat.cast_nonneg _))
private theorem taylorPower_cast {g : ℕ} (hg : 0 < g) :
    (taylorPower g : ℚ) = 2 * (g : ℚ) - 1 := by
  unfold taylorPower
  rw [Nat.cast_sub (by omega)]
  push_cast
  rfl
private theorem regular_count {n g H d : ℕ} {U : Finset K} {s : K → Polynomial K} {w}
    (A : K1_14_2_4.RegularChart U s g H n) (hw : FixedWord w U s d)
    (hg : 0 < g) (hl : 131071 ≤ d) (hh : d ≤ 164320) :
    (U.card : ℚ) ≤ (2 * density * d * (taylorPower g : ℚ) + rho d) * H + 1 := by
  have hbound : 0 ≤ (2 * density * d * (taylorPower g : ℚ) + rho d) * (H : ℚ) := by
    unfold rho
    positivity
  by_cases hc : U.card ≤ 1
  · have h : (U.card : ℚ) ≤ 1 := by exact_mod_cast hc
    linarith only [h, hbound]
  let sites := persistentNodes w U s
  let t := max 1 (d-sites.card)
  have hd : d < agreement := hh.trans_lt (by decide)
  have hs : sites.card ≤ d := persistent_card_le hw (by omega)
  have ht : 0 < t := (by decide : 0 < 1).trans_le (le_max_left _ _)
  have htp : t < p := (max_le (by omega : 1 ≤ d) (Nat.sub_le _ _)).trans_lt
    (hh.trans_lt (by decide))
  have hdt : d ≤ sites.card + t := by
    have h := le_max_right 1 (d-sites.card)
    omega
  obtain ⟨C, hreconstruct⟩ := persistent_taylor sites w hdt htp hg A.equation A.equation_degree
  let D := taylorPower t * (g * H) + ordinateBound t g * H
  have hsection := section_bounds (w := w) A ht hw.distinct C fun γ hγ =>
    hreconstruct _ _ (hw.degree γ hγ) (fun _ hi => hits_persistent hγ hi) (A.root γ hγ) (A.simple γ hγ)
  have hinc : ((agreement - sites.card : ℕ) : ℚ) * U.card ≤ ((blockLength - sites.card : ℕ) : ℚ) * D := by
    exact_mod_cast section_incidence hw D hsection
  have hden : (0 : ℚ) < ((agreement - sites.card : ℕ) : ℚ) := by
    exact_mod_cast Nat.sub_pos_of_lt (hs.trans_lt hd)
  have hcard : (U.card : ℚ) ≤ rho sites.card * (D : ℚ) := by
    rw [rho, div_mul_eq_mul_div]
    apply (le_div_iff₀ hden).mpr
    calc
      _ = ((agreement - sites.card : ℕ) : ℚ) * U.card := mul_comm _ _
      _ ≤ _ := hinc
  obtain ⟨hρ, hρt⟩ := weights hs hd (rho_at_endpoint hl hh)
  have hρb : rho sites.card * (taylorPower t : ℚ) ≤ 2 * density * d := by
    have hb : (taylorPower t : ℚ) ≤ 2 * (t : ℚ) := by
      exact_mod_cast (Nat.sub_le (2*t) 1 : taylorPower t ≤ 2*t)
    have hρ0 : 0 ≤ rho sites.card := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    have h := mul_le_mul_of_nonneg_left hb hρ0
    nlinarith only [h, hρt]
  have hsum : g + (g - 1) = taylorPower g := by unfold taylorPower; omega
  have hD : D = (taylorPower t * taylorPower g + 1) * H := by
    rw [← hsum]
    dsimp [D, ordinateBound]
    ring
  refine hcard.trans (le_add_of_le_of_nonneg ?_ zero_le_one)
  calc
    _ = (rho sites.card * (taylorPower t : ℚ) * (taylorPower g : ℚ) + rho sites.card) * H := by
      rw [hD]
      push_cast
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (add_le_add (mul_le_mul_of_nonneg_right hρb (Nat.cast_nonneg _)) hρ) (Nat.cast_nonneg _)
theorem persistent_curve {b : P3.HighBand} {u del} (M : AnchorModel u del)
    {Γ} (F : AnchoredFamily M Γ) (hband : InBand b M.overhead) : CurveTariff b M F := by
  intro T hT J g H hg hgLimit hcurve _hseed hmarks
  have hlabel : Set.InjOn M.label (T : Set K) := by
    intro γ _ η _ h
    exact sub_left_inj.mp h
  obtain ⟨U, hU, hexc, n, ⟨A⟩⟩ := regular_chart T M.label F.scalar J g H hg
    (hgLimit.trans_lt (by decide)) hcurve hlabel hmarks
  let d := degreeAt b.row.hi
  have hw : FixedWord M.word U F.scalar d := by
    refine ⟨F.distinct.mono (hU.trans hT), ?_, ?_⟩
    · intro γ hγ
      rcases (F.mark γ (hT (hU hγ))).scalar_degree with hz | hm
      · simp [hz]
      · have hd : ((F.scalar γ).natDegree : ℤ) ≤ (d : ℤ) := by
          change ((F.scalar γ).natDegree : ℤ) ≤ 131071 + M.overhead at hm
          dsimp [d, degreeAt, P1_7.degreeAt]
          have h := hband.2
          omega
        exact_mod_cast hd
    · intro γ hγ
      let m := F.mark γ (hT (hU hγ))
      exact ⟨m.bad.support, m.bad.agreement, m.scalar_hits⟩
  have hlo : 131071 ≤ d := Nat.le_add_right _ _
  have hhi : d ≤ 164320 := by
    have h := (P3_7.terminal_guards b).2.1
    dsimp [d, degreeAt, P1_7.degreeAt]
    omega
  have hregular := regular_count A hw hg hlo hhi
  have hgQ : (1 : ℚ) ≤ g := by exact_mod_cast hg
  have hexcQ : ((T \ U).card : ℚ) ≤ (taylorPower g : ℚ) * H := by exact_mod_cast hexc
  calc
    (T.card : ℚ) = ((T \ U).card : ℚ) + (U.card : ℚ) := by
      exact_mod_cast (card_sdiff_add_card_eq_card hU).symm
    _ ≤ (taylorPower g : ℚ) * H + ((2 * density * d * (taylorPower g : ℚ) + rho d) * H + 1) :=
      add_le_add hexcQ hregular
    _ ≤ (taylorPower g : ℚ) * H + ((2 * density * d * (taylorPower g : ℚ) + rho d) * H + g) :=
      add_le_add le_rfl (add_le_add le_rfl hgQ)
    _ = curveUnit b.row.hi g * H + g := by
      rw [taylorPower_cast hg]
      unfold curveUnit gap rho
      dsimp only [d]
      ring
end
end P3_7
end
section
namespace P3_7
noncomputable section
open Polynomial Finset MvPolynomial ProximityPrize.Benchmark
open scoped BigOperators
open P3 (K I node agreement blockLength)
open K1_14 (FX)
open K1_14_6 (Biform ClosedField rootPoint)
open P1_7_7 (point slice slice_subset slice_on point_injective boxMap BoxRing
  localOrd localSeed ShortCharts WeightedCut CurveScale)
open private zero_dim_count common common_agrees from ProximityPrize.SubmissionLower.UpperBranch7
open private card_le_sum_cover from ProximityPrize.SubmissionLower.Fast055
open private eval_extend extend_mem from ProximityPrize.SubmissionLower.Fast055
private theorem common_bound {word T S d} (hword : FixedWord word T S d)
    {U : Finset K} (hU : U ⊆ T) (hsize : 1 < U.card) :
    (common word U S).card ≤ d := by
  obtain ⟨γ, hγ, η, hη, hne⟩ := one_lt_card.mp hsize
  let P := S γ - S η
  have hp : P ≠ 0 := sub_ne_zero.mpr fun he => hne (hword.distinct (hU hγ) (hU hη) he)
  refine (FrobeniusLocator.Strata.root_nodes_card_le node IRSProfile.domain.injective
    P hp _ ?_).trans ((natDegree_sub_le _ _).trans (max_le (hword.degree γ (hU hγ))
      (hword.degree η (hU hη))))
  intro j hj
  change ((S γ) - (S η)).eval (node j) = 0
  rw [Polynomial.eval_sub, common_agrees hγ hj, common_agrees hη hj, sub_self]
private theorem residual_incidence {word T S d} (hword : FixedWord word T S d)
    {U : Finset K} (hU : U ⊆ T) (cap : ℚ)
    (hcap : ∀ j ∉ common word U S, ((U.filter fun γ => (S γ).eval (node j) = word j).card : ℚ) ≤ cap) :
    ((agreement - (common word U S).card : ℕ) : ℚ) * U.card ≤
      ((blockLength - (common word U S).card : ℕ) : ℚ) * cap := by
  classical
  let sites := common word U S
  let J : Finset I := univ \ sites
  let rel (γ : K) (j : I) := (S γ).eval (node j) = word j
  have hJ : J.card = blockLength - sites.card := by
    rw [card_sdiff_of_subset (subset_univ sites), card_univ, IRSProfile.card_index]
  have hrows (γ : K) (hγ : γ ∈ U) :
      ((agreement - sites.card : ℕ) : ℚ) ≤ (J.bipartiteAbove rel γ).card := by
    obtain ⟨H, hH, heval⟩ := hword.hits γ (hU hγ)
    have hcover : H \ sites ⊆ J.bipartiteAbove rel γ := fun j hj =>
      mem_filter.mpr
        ⟨mem_sdiff.mpr ⟨mem_univ _, (mem_sdiff.mp hj).2⟩, heval j (mem_sdiff.mp hj).1⟩
    exact_mod_cast (Nat.sub_le_sub_right hH sites.card).trans
      ((le_card_sdiff _ _).trans (card_le_card hcover))
  have hcols (j : I) (hj : j ∈ J) :
      ((U.bipartiteBelow rel j).card : ℚ) ≤ cap := hcap j (mem_sdiff.mp hj).2
  have he := card_nsmul_le_card_nsmul rel hrows hcols
  rw [nsmul_eq_mul, nsmul_eq_mul, hJ, mul_comm (U.card : ℚ)] at he
  exact he
structure Invoice (d w e v a b D : ℕ) : Prop where
  scale_pos : 0 < D
  ordinate : D ≤ a
  seed : D ≤ b
  degree : d < agreement
  fits : ∀ s ≤ d, D * (blockLength-s) * localOrd d w e s ≤ (agreement-s) * a ∧
    D * (blockLength-s) * localSeed d w v s ≤ (agreement-s) * b
private theorem count_step {d w e v a b D : ℕ} (hInv : Invoice d w e v a b D)
    (hcut : WeightedCut) {word T z S} (hword : FixedWord word T S d)
    (hchart : ShortCharts d w e v word T z S)
    {U : Finset K} (hU : U ⊆ T) (hsize : 1 < U.card) (P : Ideal (BoxRing a b))
    (hP : P.IsPrime) (hbase : RingHom.ker (boxMap a b) ≤ P)
    (hdim : 0 < (affineHilbertPolynomial P).natDegree)
    (hpoints : ∀ γ ∈ U, point a b z S γ ∈ zeroLocus ClosedField P)
    {c : ℚ} (hc : 0 < c)
    (hchildren : ∀ (V : Finset K), V ⊆ U → ∀ (Q : Ideal (BoxRing a b)), Q.IsPrime →
      RingHom.ker (boxMap a b) ≤ Q →
      (affineHilbertPolynomial Q).natDegree + 1 = (affineHilbertPolynomial P).natDegree →
      (∀ γ ∈ V, point a b z S γ ∈ zeroLocus ClosedField Q) →
      c * V.card ≤ affineDegree Q) :
    (D : ℚ) * c * U.card ≤ affineDegree P := by
  classical
  let sites := common word U S
  let s := sites.card
  let r := D * (blockLength-s)
  let t := agreement-s
  have hs : s ≤ d := common_bound hword hU hsize
  have ht : 0 < t := Nat.sub_pos_of_lt (hs.trans_lt hInv.degree)
  have hn : 0 < blockLength-s :=
    Nat.sub_pos_of_lt (hs.trans_lt (hInv.degree.trans (by decide)))
  have hr : 0 < r := Nat.mul_pos hInv.scale_pos hn
  have ha := hInv.scale_pos.trans_le hInv.ordinate
  have hb := hInv.scale_pos.trans_le hInv.seed
  let : P.IsPrime := hP
  obtain ⟨cut, hcut_box, hcut_eval⟩ := hchart U hU sites hs
    (fun _ hγ _ hj => common_agrees hγ hj)
  let ι := algebraMap FX ClosedField
  have hsection (j : I) (hj : j ∉ sites) :
      (r : ℚ) * (c * ((U.filter fun γ => (S γ).eval (node j) = word j).card : ℚ)) ≤
        (t : ℚ) * affineDegree P := by
    let V := U.filter fun γ => (S γ).eval (node j) = word j
    obtain ⟨q, hq⟩ := bidegreeMap_surjective (R := ClosedField) ha hb (MvPolynomial.map ι (cut j))
    have heval (γ : K) (hγ : γ ∈ U) :
        aeval (point a b z S γ) q = 0 ↔ (S γ).eval (node j) = word j := by
      rw [point, aeval_monomialPoint, ← bidegreeMap_eq_monomialMap, hq]
      change MvPolynomial.eval (ι ∘ rootPoint (z γ) (S γ)) (MvPolynomial.map ι (cut j)) = 0 ↔ _
      rw [eval_extend, ← map_zero ι, ι.injective.eq_iff]
      exact hcut_eval γ hγ j
    have hproper : q ∉ P := by
      intro hqP
      apply hj
      exact mem_filter.mpr ⟨mem_univ _, fun γ hγ => (heval γ hγ).mp (hpoints γ hγ q hqP)⟩
    let Qs := (P ⊔ Ideal.span {q}).minimalPrimesFinset
    have hdeg : (r : ℚ) * (∑ Q ∈ Qs, affineDegree Q) ≤ (t : ℚ) * affineDegree P :=
      hcut a b _ _ r t ha hb hr ht (hInv.fits s hs).1 (hInv.fits s hs).2
        P hP hbase hdim q hproper (by rw [hq]; exact extend_mem (hcut_box j))
    have hcover : V.card ≤ ∑ Q ∈ Qs, (slice z S V Q).card := by
      apply card_le_sum_cover
      intro γ hγ
      obtain ⟨hγU, hv⟩ := mem_filter.mp hγ
      have hγP : point a b z S γ ∈ zeroLocus ClosedField (P ⊔ Ideal.span {q}) :=
        mem_zeroLocus_sup_span_singleton_iff.mpr ⟨hpoints γ hγU, (heval γ hγU).mpr hv⟩
      obtain ⟨Q, hQ, hγQ⟩ := exists_retainedMinimalPrime_of_mem_zeroLocus _ 1 _ hγP (by simp)
      exact ⟨Q, Ideal.mem_minimalPrimesFinset.mpr (Ideal.mem_retainedMinimalPrimes.mp hQ).1,
        mem_filter.mpr ⟨hγ, hγQ⟩⟩
    have hparts (Q : Ideal (BoxRing a b)) (hQ : Q ∈ Qs) :
        c * ((slice z S V Q).card : ℚ) ≤ affineDegree Q := by
      have hmin := Ideal.mem_minimalPrimesFinset.mp hQ
      exact hchildren _ ((slice_subset Q).trans (filter_subset _ _)) Q hmin.isPrime
        (hbase.trans (le_sup_left.trans hmin.le))
        (principalCut_natDegree_affineHilbertPolynomial_add_one hproper hmin)
        (fun _ hγ => slice_on Q hγ)
    have hcoverQ : (V.card : ℚ) ≤ ∑ Q ∈ Qs, ((slice z S V Q).card : ℚ) := by
      exact_mod_cast hcover
    have hsum : c * (V.card : ℚ) ≤ ∑ Q ∈ Qs, affineDegree Q := by
      refine (mul_le_mul_of_nonneg_left hcoverQ hc.le).trans ?_
      rw [mul_sum]
      exact sum_le_sum hparts
    exact (mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg r)).trans hdeg
  let cap : ℚ := (t : ℚ) * affineDegree P / ((r : ℚ) * c)
  have hrc : 0 < (r : ℚ) * c := mul_pos (Nat.cast_pos.mpr hr) hc
  have hinc := residual_incidence hword hU cap (fun j hj => by
    apply (le_div_iff₀ hrc).mpr
    calc
      _ = (r : ℚ) * (c * ((U.filter fun γ => (S γ).eval (node j) = word j).card : ℚ)) := by ring
      _ ≤ _ := hsection j hj)
  change (t : ℚ) * U.card ≤ ((blockLength-s : ℕ) : ℚ) * cap at hinc
  have hnQ : (0 : ℚ) < ((blockLength-s : ℕ) : ℚ) := Nat.cast_pos.mpr hn
  have htQ : (0 : ℚ) < (t : ℚ) := Nat.cast_pos.mpr ht
  apply le_of_mul_le_mul_left _ (mul_pos hnQ htQ)
  calc
    _ = ((r : ℚ) * c) * ((t : ℚ) * U.card) := by simp only [r, Nat.cast_mul]; ring
    _ ≤ ((r : ℚ) * c) * (((blockLength-s : ℕ) : ℚ) * cap) :=
      mul_le_mul_of_nonneg_left hinc hrc.le
    _ = _ := by dsimp only [cap]; field_simp [hrc.ne']
theorem count_cover {d w e v a b D : ℕ} (hInv : Invoice d w e v a b D)
    (hcut : WeightedCut) (hscale : CurveScale) {word T z S} (hword : FixedWord word T S d)
    (hchart : ShortCharts d w e v word T z S) (hz : Set.InjOn z (T : Set K))
    (Ps : Finset (Ideal (BoxRing a b)))
    (hPs : ∀ P ∈ Ps, P.IsPrime ∧ RingHom.ker (boxMap a b) ≤ P ∧
      (affineHilbertPolynomial P).natDegree = 2)
    (hcover : ∀ γ ∈ T, ∃ P ∈ Ps, point a b z S γ ∈ zeroLocus ClosedField P) :
    (D : ℚ)^2 * T.card ≤ (∑ P ∈ Ps, affineDegree P) + (D : ℚ)^2 * Ps.card := by
  classical
  have hinj := point_injective (hInv.scale_pos.trans_le hInv.ordinate)
    (hInv.scale_pos.trans_le hInv.seed) (S := S) hz
  have curve {U : Finset K} (hU : U ⊆ T) (P : Ideal (BoxRing a b))
      (hP : P.IsPrime) (hbase : RingHom.ker (boxMap a b) ≤ P)
      (hdim : (affineHilbertPolynomial P).natDegree = 1)
      (hpoints : ∀ γ ∈ U, point a b z S γ ∈ zeroLocus ClosedField P) :
      (D : ℚ) * U.card ≤ affineDegree P := by
    by_cases hsize : 1 < U.card
    · simpa only [mul_one] using
        count_step hInv hcut hword hchart hU hsize P hP hbase (by omega) hpoints
          (by norm_num : (0 : ℚ) < 1) (fun V hv Q _ _ hdimQ hpointQ => by
            rw [one_mul]
            exact zero_dim_count (hv.trans hU) hinj Q (by omega) hpointQ)
    · have hu : (U.card : ℚ) ≤ 1 := by exact_mod_cast (show U.card ≤ 1 by omega)
      calc
        _ ≤ (D : ℚ) * 1 := mul_le_mul_of_nonneg_left hu (Nat.cast_nonneg D)
        _ ≤ affineDegree P := by
          rw [mul_one]
          exact hscale a b D hInv.scale_pos hInv.ordinate hInv.seed P hP hbase hdim
  have surface (P : Ideal (BoxRing a b)) (hP : P ∈ Ps) :
      (D : ℚ)^2 * ((slice z S T P).card : ℚ) ≤ affineDegree P + (D : ℚ)^2 := by
    obtain ⟨hp, hk, hd⟩ := hPs P hP
    by_cases hsize : 1 < (slice z S T P).card
    · rw [pow_two]
      exact (count_step hInv hcut hword hchart (slice_subset P) hsize P hp hk (by omega)
        (fun _ hγ => slice_on P hγ) (Nat.cast_pos.mpr hInv.scale_pos)
        (fun V hv Q hQ hQk hQd hQV => curve (hv.trans (slice_subset P)) Q hQ hQk (by omega) hQV)).trans
          (le_add_of_nonneg_right (by positivity))
    · have hu : ((slice z S T P).card : ℚ) ≤ 1 := by
        exact_mod_cast (show (slice z S T P).card ≤ 1 by omega)
      calc
        _ ≤ (D : ℚ)^2 * 1 := mul_le_mul_of_nonneg_left hu (by positivity)
        _ ≤ _ := by rw [mul_one]; exact le_add_of_nonneg_left (affineDegree_nonneg P)
  have hsum : T.card ≤ ∑ P ∈ Ps, (slice z S T P).card := by
    apply card_le_sum_cover
    intro γ hγ
    obtain ⟨P, hP, hγP⟩ := hcover γ hγ
    exact ⟨P, hP, mem_filter.mpr ⟨hγ, hγP⟩⟩
  have hsumQ : (T.card : ℚ) ≤ ∑ P ∈ Ps, ((slice z S T P).card : ℚ) := by exact_mod_cast hsum
  calc
    _ ≤ (D : ℚ)^2 * ∑ P ∈ Ps, ((slice z S T P).card : ℚ) :=
      mul_le_mul_of_nonneg_left hsumQ (by positivity)
    _ ≤ ∑ P ∈ Ps, (affineDegree P + (D : ℚ)^2) := by
      rw [mul_sum]
      exact sum_le_sum surface
    _ = _ := by rw [sum_add_distrib, sum_const, nsmul_eq_mul, mul_comm (Ps.card : ℚ)]
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
theorem window_nat {b : HighBand} {w : ℤ} (hw : InBand b w) :
    b.row.lo ≤ w.toNat ∧ w.toNat ≤ b.row.hi := by
  obtain ⟨hl, hh⟩ := hw
  omega
theorem tested_spec (b : HighBand) (x : Test b) :
    Listed b (tested b x) ∧ (tested b x).shape.m = (terminal b).shape.m ∧
    (tested b x).shape.B = (terminal b).shape.B ∧ (tested b x).shape.J = (terminal b).shape.J ∧
    (tested b x).shape.U ≤ (terminal b).shape.U := by
  cases x with
  | none => exact ⟨Or.inl rfl, rfl, rfl, rfl, le_rfl⟩
  | some i => exact ⟨Or.inr (Or.inr ⟨i, rfl⟩), rfl, rfl, rfl, (grade_checked b i).sub⟩
private theorem order_of_full {b u del} {M : AnchorModel u del} {Γ} {F : AnchoredFamily M Γ}
    {rows : Banks} (src : Source b M F rows) (hw : InBand b M.overhead)
    (x : Test b) {q : Surface} (hq : Parent q) (hv : BankPass rows (terminal b).shape q)
    {W} (hW : W < (tested b x).shape.m * agreement) {P : Jet}
    (hP : P ∈ rows (tested b x).shape W) :
    OrderAt q P (contactPower M.overhead.toNat (tested b x).shape W) := by
  let h := M.overhead.toNat
  let t := tested b x
  obtain ⟨ht, hm, hb, hj, hu⟩ := tested_spec b x
  have hchar : t.shape.m * agreement < p := hm ▸ (terminal_guards b).2.2.2.1
  apply K1_14_3R_1.proof _ _ _ hq
  · have hd := Nat.div_le_self (fullCutoff t.shape - W) (2*h)
    change 1 + (fullCutoff t.shape - W)/(2*h) < p
    change W < t.shape.m * agreement at hW
    unfold fullCutoff at *
    omega
  intro a c hac
  change a + c < 1 + (fullCutoff t.shape - W)/(2*h) at hac
  have hh : 0 < h := (terminal_guards b).1.trans_le (window_nat hw).1
  have hc := (Nat.le_div_iff_mul_le (by omega : 0 < 2*h)).mp
    (show a+c ≤ (fullCutoff t.shape - W)/(2*h) by omega)
  rw [Nat.mul_comm (a+c), Nat.mul_add] at hc
  have top : fullCutoff t.shape = fullCutoff (terminal b).shape :=
    congrArg (fun m => m * agreement - 1) hm
  have hwc : W ≤ fullCutoff t.shape := by
    change W < t.shape.m * agreement at hW
    unfold fullCutoff
    omega
  have hw' : W + 2*h*a + 2*h*c ≤ fullCutoff (terminal b).shape := by omega
  have ha := src.shift t ht W P hP 0 a
  have hc' := src.shift t ht _ _ ha 1 c
  exact hv _ (src.nested t ht _ (Or.inl rfl) hm hb hj hu _ _ hw' hc')
theorem trace_of_full {b u del} {M : AnchorModel u del} {Γ} {F : AnchoredFamily M Γ}
    {rows : Banks} (src : Source b M F rows) (hw : InBand b M.overhead)
    {qs : Finset Surface} (hq : ∀ q ∈ qs, Parent q)
    (hp : ∀ q ∈ qs, BankPass rows (terminal b).shape q) {f : Equation}
    (hf : ProjectedProduct qs f) (x : Test b) :
    TerminalTrace M.overhead.toNat (tested b x) rows f := by
  have ht := (tested_spec b x).1
  refine ⟨src.floor_bound _ ht, src.shape _ ht, src.leading _ ht, ?_⟩
  intro W hW P hP hn
  exact hf.divides_leading P _ hn
    (fun q h => order_of_full src hw x (hq q h) (hp q h) hW hP)
theorem grade_of_rejections {b : HighBand} {f : Equation} (hp : 0 < f.natDegree)
    (reject : ∀ x : Test b, threshold b x ≤ f.natDegree →
      seedThreshold b x ≤ seedDegree f → False) :
    ∃ i : GradeIndex b, f.natDegree = i.val+1 ∧ SeedBound f ((grades b).get i).seedCap := by
  have he : f.natDegree ≤ (grades b).length := by
    by_contra! hlo
    exact reject none hlo (Nat.zero_le _)
  let i : GradeIndex b := ⟨f.natDegree-1, by omega⟩
  have hidx : f.natDegree = i.val+1 := by dsimp [i]; omega
  refine ⟨i, hidx, (seedDegree_le_iff _ _).mp ?_⟩
  by_contra! hlow
  exact reject (some i) hidx.ge hlow
end
end P3_7
end
section
namespace P3_7
open P3 (HighBand agreement blockLength)
open P1_7_7 (localOrd localSeed)
open private coordinate_bounds from ProximityPrize.SubmissionLower.UpperBranch7
def ordinateFee (lo hi e : ℕ) := muNum hi + 2 * (lambdaNum hi * quotientOrder lo) * (e - 1)
def seedFee (lo hi v : ℕ) := 2 * hi * muNum hi + 2 * (lambdaNum hi * quotientOrder lo) * v
theorem band_invoice {b : HighBand} {w : ℕ} (hwlo : b.row.lo ≤ w) (hwhi : w ≤ b.row.hi)
    (e v : ℕ) :
    Invoice (131071+w) w e v (ordinateFee b.row.lo b.row.hi e) (seedFee b.row.lo b.row.hi v)
      (scale b.row.hi) := by
  obtain ⟨hlo, hhi, _, _, _⟩ := terminal_guards b
  have hdhi : degreeAt b.row.hi < agreement := by
    change 131071 + b.row.hi < 179983
    omega
  have hd : 131071+w < agreement := (Nat.add_le_add_left hwhi _).trans_lt hdhi
  have hA : agreement ≤ blockLength := by decide
  have hD : 0 < scale b.row.hi := Nat.mul_pos (by decide) (Nat.sub_pos_of_lt hdhi)
  have hm : scale b.row.hi ≤ muNum b.row.hi :=
    Nat.mul_le_mul_left _ (Nat.sub_le_sub_right hA _)
  have hpos : 1 ≤ 2*b.row.hi := by omega
  refine ⟨hD, hm.trans (Nat.le_add_right _ _), ?_, hd, ?_⟩
  · exact hm.trans ((by
      simpa only [one_mul] using Nat.mul_le_mul_right (muNum b.row.hi) hpos :
      muNum b.row.hi ≤ 2*b.row.hi*muNum b.row.hi).trans (Nat.le_add_right _ _))
  · intro s hs
    have hord : (131071+w) - 2*w ≤ quotientOrder b.row.lo := by
      unfold quotientOrder P1_7.quotientOrder
      omega
    exact coordinate_bounds hA (Nat.add_le_add_left hwhi _) hdhi hwhi hord hs
theorem fee_of_bound {lo hi e v count : ℕ} (hD : 0 < scale hi)
    (hcount : ((scale hi : ℕ) : ℚ)^2 * count ≤
      ((e * (seedFee lo hi v)^2 + 2*v*(ordinateFee lo hi e)*(seedFee lo hi v) : ℕ) : ℚ) +
        ((scale hi : ℕ) : ℚ)^2 * e) :
    count ≤ persistentFee lo hi e v := by
  let D := (scale hi)^2
  let num := e * (seedFee lo hi v)^2 + 2*v*(ordinateFee lo hi e)*(seedFee lo hi v)
  have hd : 0 < D := pow_pos hD _
  have h : D * count ≤ num + D * e := by exact_mod_cast hcount
  have hmul : (count-e) * D ≤ num := by
    rw [Nat.sub_mul, Nat.mul_comm count, Nat.mul_comm e]
    omega
  have hdiv := (Nat.le_div_iff_mul_le hd).mpr (hmul.trans (Nat.le_add_right num (D-1)))
  change count ≤ (num + (D-1)) / D + e
  omega
end P3_7
end
section
namespace P3_7
noncomputable section
open Polynomial MvPolynomial
open P3 (AnchorModel AnchoredFamily HighBand I K agreement node p)
open K1_14 (Equation FX L SeedBound seedEmbedding liftPoly)
open K1_14_1 (PoleData CRTLift MarkResidues seedPair)
open P1_7_7 (CRTChart poleProduct sheet_cover curve_scale_of_cut)
open private pole_data from ProximityPrize.SubmissionLower.UpperBranch7
open scoped BigOperators
theorem persistent_count {b : HighBand} {u del} (M : AnchorModel u del)
    {Γ} (F : AnchoredFamily M Γ) (hband : InBand b M.overhead)
    {H} (hH : AdjacentChart M F H) (i : GradeIndex b) {f : Equation}
    (hf : Reduced f) (hseed : SeedBound f ((grades b).get i).seedCap) :
    RegularCount M F f (persistentFee b.row.lo b.row.hi f.natDegree ((grades b).get i).seedCap) := by
  intro T hT hroots
  let w := M.overhead.toNat
  let d := 131071 + w
  let e := f.natDegree
  let v := ((grades b).get i).seedCap
  obtain ⟨hwlo, hwhi⟩ := window_nat hband
  obtain ⟨hlo, hhi, _, _, _⟩ := terminal_guards b
  have hw : 0 < w := hlo.trans_le hwlo
  have h2w : 2 * w ≤ d := by dsimp only [d]; omega
  have hInv := band_invoice hwlo hwhi e v
  have hdp : d < p := hInv.degree.trans (by decide)
  have hword : FixedWord M.word T F.scalar d := by
    refine ⟨F.distinct.mono hT, ?_, ?_⟩
    · intro γ hγ
      rcases (F.mark γ (hT hγ)).scalar_degree with hz | hdeg
      · simp only [hz, natDegree_zero, Nat.zero_le]
      · change ((F.scalar γ).natDegree : ℤ) ≤ 131072 - 1 + M.overhead at hdeg
        have hd' : ((F.scalar γ).natDegree : ℤ) ≤ 131071 + (w : ℤ) := by
          dsimp only [w]
          omega
        exact_mod_cast hd'
    · intro γ hγ
      let mark := F.mark γ (hT hγ)
      exact ⟨mark.bad.support, mark.bad.agreement, mark.scalar_hits⟩
  have hz : Set.InjOn M.label (T : Set K) := fun _ _ _ _ h => sub_left_inj.mp h
  obtain ⟨CRT, hCRT⟩ := P1_7_7_1.proof u del (asP1Model M) Γ (asP1Family M F) H hw hH
  obtain ⟨hmonic, hdeg, hcenter, hnodes⟩ :=
    pole_data (M := asP1Model M) (F := asP1Family M F) hH
  have hchart := P1_7_7_2.proof d w e v hw h2w hdp (poleProduct H) hmonic hdeg hcenter hnodes
    f hf.1 le_rfl hseed T M.label F.scalar M.word hword.degree hroots CRT
    (fun γ hγ => hCRT γ (hT hγ))
  obtain ⟨Ps, hPs, hcard, hsum, hcover⟩ := sheet_cover
    (hInv.scale_pos.trans_le hInv.ordinate) (hInv.scale_pos.trans_le hInv.seed)
    f hf.1 (show f.natDegree ≤ e from le_rfl) hseed T M.label F.scalar hroots
  have hcount := count_cover hInv P1_7_7_3.proof (curve_scale_of_cut P1_7_7_3.proof) hword hchart hz Ps hPs hcover
  apply fee_of_bound hInv.scale_pos
  refine hcount.trans (add_le_add hsum ?_)
  exact mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hcard) (by positivity)
end
end P3_7
end
section
namespace P3_7
noncomputable section
open Finset Polynomial MvPolynomial
open P3 (agreement)
open K1_14 (Shape shapeSum Banks Equation FX Jet slots triangle SeedBound)
open K1_14_3 (RowCaps)
open K1_14_4 (gradeWidth seedDegree seedDegree_pow)
open P1_7_5 (kept)
open private position_sum from ProximityPrize.SubmissionLower.UpperBranch5
open private rank_joint_multiples_le gradeCapacity_eq from ProximityPrize.SubmissionLower.UpperBranch5
open private shapeSum_swap from ProximityPrize.SubmissionLower.Fast072
open private finrank_le_grades mem_filtered from ProximityPrize.SubmissionLower.Fast069
def cutoffCapacity (h : ℕ) (s : Shape) (E v W : ℕ) : ℕ :=
  shapeSum s fun q j =>
    if q*(131071-h) ≤ W+j then
      kept s.U v ((q-j)/E) (contactPower h s W - j)
    else 0
private def gradeCapacity (h : ℕ) (s : Shape) (E v W j : ℕ) : ℕ :=
  let r := contactPower h s W - j
  (gradeWidth (131071-h) s.B W j - r*E) * slots s.U (r*v)
private theorem cutoffCapacity_eq (h : ℕ) (s : Shape) (E v W : ℕ)
    (hk : 0 < 131071-h) (he : 0 < E) :
    (∑ j ∈ range (s.J+1), gradeCapacity h s E v W j) = cutoffCapacity h s E v W := by
  rw [cutoffCapacity, ← shapeSum_swap]
  apply sum_congr rfl
  intro j _
  exact gradeCapacity_eq _ _ _ _ _ _ _ _ hk he
set_option backward.isDefEq.respectTransparency false in
theorem cutoff_finrank_le (h : ℕ) (s : Shape) (E v W : ℕ) (V : Submodule FX Jet)
    {f : Equation} (hf : f ≠ 0) (hE : E ≤ f.natDegree) (hv : v ≤ seedDegree f)
    (hk : 0 < 131071-h) (he : 0 < E)
    (hcaps : ∀ P ∈ V, RowCaps P s)
    (hlead : ∀ P ∈ V, P ≠ 0 →
      (P.leadingCoeff.natDegree + P.natDegree) * (131071-h) ≤ W + P.natDegree)
    (hdvd : ∀ P ∈ V, P ≠ 0 → f ^ (contactPower h s W - P.natDegree) ∣ P.leadingCoeff) :
    Module.finrank FX V ≤ cutoffCapacity h s E v W := by
  have hrow {P : Jet} (hP : P ∈ V) (hn : P ≠ 0) :
      P.leadingCoeff.natDegree + P.natDegree ≤ s.B ∧ P.natDegree ≤ s.J ∧
      SeedBound P.leadingCoeff s.U := by
    have ha : (P.coeff P.natDegree).coeff P.leadingCoeff.natDegree ≠ 0 := by
      rw [coeff_natDegree, coeff_natDegree]
      exact leadingCoeff_ne_zero.mpr (leadingCoeff_ne_zero.mpr hn)
    obtain ⟨hB, hJ, _⟩ := hcaps P hP _ _ ha
    refine ⟨hB, hJ, fun i => ?_⟩
    by_cases hi : P.leadingCoeff.coeff i = 0
    · simp [hi]
    · rw [← coeff_natDegree] at hi ⊢
      exact (hcaps P hP _ _ hi).2.2
  rw [← cutoffCapacity_eq h s E v W hk he]
  refine finrank_le_grades (F := FX) (A := Equation) V (gradeCapacity h s E v W)
    (s.J+1) ?_ ?_
  · intro j
    let r := contactPower h s W - j
    apply rank_joint_multiples_le _ (g := f^r) (pow_ne_zero r hf)
    · rw [Polynomial.natDegree_pow]
      exact Nat.mul_le_mul_left _ hE
    · rw [seedDegree_pow hf]
      exact Nat.mul_le_mul_left _ hv
    · rintro c ⟨⟨P, hP⟩, rfl⟩ hc
      change P.coeff j ≠ 0 at hc
      obtain ⟨hpV, hd⟩ := mem_filtered.mp hP
      have hn : P ≠ 0 := by
        intro hz
        exact hc (by simp [hz])
      have hj : P.natDegree = j :=
        le_antisymm (Nat.le_of_lt_succ ((natDegree_lt_iff_degree_lt hn).2 hd))
          (le_natDegree_of_ne_zero hc)
      obtain ⟨hB, _, hseed⟩ := hrow hpV hn
      have hwidth := hlead P hpV hn
      have hdiv := hdvd P hpV hn
      rw [hj] at hB hwidth hdiv
      change (P.coeff j).natDegree < _ ∧ SeedBound (P.coeff j) _ ∧ _ ∣ P.coeff j
      rw [← hj, coeff_natDegree, hj]
      refine ⟨?_, hseed, hdiv⟩
      have hd := (Nat.le_div_iff_mul_le hk).2 hwidth
      unfold gradeWidth
      omega
  · intro P hp
    by_cases hn : P = 0
    · simp [hn]
    · exact (natDegree_lt_iff_degree_lt hn).1 (Nat.lt_succ_of_le (hrow hp hn).2.1)
theorem cutoff_total (h : ℕ) (s : Shape) (E v : ℕ) (hh : 0 < 2*h) (hk : 1 ≤ 131071-h) :
    (∑ W ∈ range (s.m*agreement), cutoffCapacity h s E v W) + jointGain h s E v =
      triangle s.U * shapeSum s (fun q j => s.m*agreement+j-q*(131071-h)) := by
  have hswap (F : ℕ → ℕ → ℕ → ℕ) :
      (∑ W ∈ range (s.m*agreement), shapeSum s (F W)) =
        shapeSum s (fun q j => ∑ W ∈ range (s.m*agreement), F W q j) := by
    unfold shapeSum
    rw [sum_comm]
    apply sum_congr rfl
    intro q _
    rw [sum_comm]
  simp only [cutoffCapacity, jointGain]
  rw [hswap]
  simp only [shapeSum, ← sum_add_distrib, mul_sum]
  apply sum_congr rfl
  intro q _
  apply sum_congr rfl
  intro j hj
  have hjq : j ≤ q := (Nat.le_of_lt_succ (mem_range.mp hj)).trans (min_le_left _ _)
  have hq : q ≤ q*(131071-h) := by simpa using Nat.mul_le_mul_left q hk
  exact position_sum (s.m*agreement) (2*h) (q*(131071-h)) j s.U v ((q-j)/E)
    (hjq.trans hq) hh
private theorem trace_rank_le {h E v W : ℕ} {t : Bank}
    {rows : K1_14.Banks} {f : K1_14.Equation} (ht : TerminalTrace h t rows f)
    (hne : f ≠ 0) (hE : E ≤ f.natDegree) (hv : v ≤ K1_14_4.seedDegree f)
    (hk : 0 < 131071 - h) (he : 0 < E) (hW : W < t.shape.m * agreement) :
    Module.finrank FX (rows t.shape W) ≤ cutoffCapacity h t.shape E v W :=
  cutoff_finrank_le h t.shape E v W (rows t.shape W) (f := f) hne hE hv hk he
    (fun P hP => ht.shape W P hP)
    (fun P hP hn => ht.leading W P hP hn)
    (fun P hP hn => ht.divides W hW P hP hn)
theorem joint_loss {b : P3.HighBand} {h : ℕ} (hl : b.row.lo ≤ h) (hu : h ≤ b.row.hi)
    (x : Test b) {rows f} (hf : Reduced f) (ht : TerminalTrace h (tested b x) rows f)
    (hE : threshold b x ≤ f.natDegree) (hv : seedThreshold b x ≤ seedDegree f) :
    jointGain h (tested b x).shape (threshold b x) (seedThreshold b x) ≤ debit h (tested b x) := by
  obtain ⟨hlo, hhi, htop, _, hwidth⟩ := terminal_guards b
  obtain ⟨_, hm, hB, _, _⟩ := tested_spec b x
  have hh : 0 < 2*h := by omega
  have hk : 0 < 131071-h := by omega
  have he : 0 < threshold b x := by cases x <;> exact Nat.succ_pos _
  have hne : f ≠ 0 := by
    intro hz
    have hpos := hf.1
    simp [hz] at hpos
  let t := tested b x
  let top := t.shape.m*agreement
  have htopPos : 0 < top := by
    change 0 < (tested b x).shape.m*agreement
    rwa [hm]
  have hbWidth : t.shape.B*(131071-h) ≤ top := by
    change (tested b x).shape.B*(131071-h) ≤ (tested b x).shape.m*agreement
    rw [hm, hB]
    exact (Nat.mul_le_mul_left _ (Nat.sub_le_sub_left hl _)).trans hwidth
  have htopSub : top-1+1 = top := by omega
  have hraw : ∀ q ≤ t.shape.B, ∀ j ≤ min q t.shape.J,
      q*(131071-h) ≤ top-1+1+j := by
    intro q hq j _
    rw [htopSub]
    exact (Nat.mul_le_mul_right _ hq).trans (hbWidth.trans (by omega : top ≤ top+j))
  have hmin := ht.floor_bound (top-1) (show top-1 < top by omega) hraw
  change triangle t.shape.U * shapeSum t.shape (fun q j => top-1+1+j-q*(131071-h)) ≤
    debit h t + ∑ W ∈ range (top-1+1), Module.finrank FX (rows t.shape W) at hmin
  rw [htopSub] at hmin
  have hmax : (∑ W ∈ range top, Module.finrank FX (rows t.shape W)) ≤
      ∑ W ∈ range top, cutoffCapacity h t.shape (threshold b x) (seedThreshold b x) W := by
    apply sum_le_sum
    intro W hW
    exact trace_rank_le ht hne hE hv hk he (mem_range.mp hW)
  have htotal := cutoff_total h t.shape (threshold b x) (seedThreshold b x) hh hk
  change (∑ W ∈ range top, cutoffCapacity h t.shape (threshold b x) (seedThreshold b x) W) +
    jointGain h t.shape (threshold b x) (seedThreshold b x) =
    triangle t.shape.U * shapeSum t.shape (fun q j => top+j-q*(131071-h)) at htotal
  change jointGain h t.shape (threshold b x) (seedThreshold b x) ≤ debit h t
  omega
end
end P3_7
end
section
namespace P3_7
noncomputable section
open Polynomial
open P3 (HighBand AnchorModel AnchoredFamily K)
open K1_14 (Banks Equation SeedBound atMark graphEval)
open K1_14_4 (seedDegree seedDegree_le_iff)
def c1 : Prop :=
  ∀ (b : HighBand) u del (M : AnchorModel u del) Γ (F : AnchoredFamily M Γ),
    InBand b M.overhead → M.shift ∉ Γ → ∀ H, AdjacentChart M F H →
    ∃ rows : Banks, Source b M F rows
def c2 : Prop :=
  ∀ (b : HighBand) u del (M : AnchorModel u del) Γ (F : AnchoredFamily M Γ),
    InBand b M.overhead → M.shift ∉ Γ → ∀ rows, Source b M F rows →
    Nonempty (Pairs b M.overhead.toNat rows)
def c3 : Prop :=
  ∀ (b : HighBand) u del (M : AnchorModel u del) Γ (F : AnchoredFamily M Γ),
    InBand b M.overhead → M.shift ∉ Γ → ∀ H, AdjacentChart M F H →
    (b.row.lo < 7773 → CurveTariff b M F) →
    ∀ rows, Source b M F rows → ∀ pairs : Pairs b M.overhead.toNat rows,
    Nonempty (PrefixInventory b M F pairs)
def c4 : Prop :=
  ∀ (b : HighBand) h, b.row.lo ≤ h → h ≤ b.row.hi → ∀ x : Test b,
    debit h (tested b x) < jointGain h (tested b x).shape (threshold b x) (seedThreshold b x)
def c5 : Prop :=
  ∀ (b : HighBand) u del (M : AnchorModel u del) Γ (F : AnchoredFamily M Γ),
    InBand b M.overhead → M.shift ∉ Γ → ∀ H, AdjacentChart M F H →
    ∀ (i : GradeIndex b) f, Reduced f → f.natDegree = i.val+1 → 3 ≤ f.natDegree →
    0 < seedDegree f → SeedBound f ((grades b).get i).seedCap →
    RegularCount M F f (tangentFee b.row.lo b.row.hi f.natDegree ((grades b).get i).seedCap)
private theorem retained_count (h5 : c5) {b u del}
    (M : AnchorModel u del) {Γ} (F : AnchoredFamily M Γ)
    (hw : InBand b M.overhead) (hshift : M.shift ∉ Γ) {H} (hH : AdjacentChart M F H)
    (T : Finset K) (hT : T ⊆ Γ) (f : Equation) (hf : Reduced f)
    (i : GradeIndex b) (he : f.natDegree = i.val+1) (hs : SeedBound f ((grades b).get i).seedCap)
    (hr : ∀ γ ∈ T, atMark f (M.label γ) (F.scalar γ) = 0) : T.card ≤ b.row.retained := by
  classical
  let v := ((grades b).get i).seedCap
  have cert := grade_checked b i
  rw [← he] at cert
  have hprice : wholePrice b.row.lo b.row.hi f.natDegree v ≤ b.row.retained := cert.fee
  by_cases hzero : seedDegree f = 0
  · have hfix := P1_7.fixed_count (asP1Model M) (asP1Family M F) T hT hf.1 ((seedDegree_le_iff f 0).mp hzero.le) hr
    exact hfix.trans ((sheets_le_price _ _ _ _).trans hprice)
  have hpos := Nat.pos_of_ne_zero hzero
  have hv : v ≠ 0 := Nat.ne_of_gt (hpos.trans_le ((seedDegree_le_iff _ _).mpr hs))
  let bad := T.filter fun γ => graphEval (M.label γ) (f.resultant f.derivative) = 0
  have hb : bad ⊆ T := Finset.filter_subset _ _
  have hbad := P1_7.resultant_count (asP1Model M) hf hs cert.separant bad
    (fun _ hγ => (Finset.mem_filter.mp hγ).2)
  have hreg : ∀ γ ∈ T \ bad, regularRoot f (M.label γ) (F.scalar γ) := by
    intro γ hγ
    obtain ⟨ht, hn⟩ := Finset.mem_sdiff.mp hγ
    exact P1_7.regular_of_resultant hf.1 (hr γ ht) (fun hz => hn (Finset.mem_filter.mpr ⟨ht,hz⟩))
  have hpartition := Finset.card_sdiff_add_card_eq_card hb
  have hsub : T \ bad ⊆ Γ := Finset.sdiff_subset.trans hT
  apply le_trans _ hprice
  by_cases hsmall : f.natDegree ≤ 2
  · have hreg' := persistent_count M F hw hH i hf hs _ hsub hreg
    simp only [wholePrice, ite_eq_right hv, ite_eq_left hsmall]
    change bad.card ≤ singularFee f.natDegree v at hbad
    change (T \ bad).card ≤ persistentFee b.row.lo b.row.hi f.natDegree v at hreg'
    omega
  · have hreg' := h5 b u del M Γ F hw hshift H hH i f hf he (by omega) hpos hs _ hsub hreg
    simp only [wholePrice, ite_eq_right hv, ite_eq_right hsmall]
    change bad.card ≤ singularFee f.natDegree v at hbad
    change (T \ bad).card ≤ tangentFee b.row.lo b.row.hi f.natDegree v at hreg'
    omega
theorem of_children (h1 : c1) (h2 : c2) (h3 : c3) (h4 : c4)
    (h5 : c5) : P3.c7 := by
  classical
  intro b u del M Γ F hlo hhi
  have hw : InBand b M.overhead := ⟨hlo,hhi⟩
  let regular := Γ.erase M.shift
  have hreg : regular ⊆ Γ := Finset.erase_subset _ _
  have hshift : M.shift ∉ regular := Finset.notMem_erase _ _
  let G : AnchoredFamily M regular :=
    ⟨F.scalar, fun γ hγ => F.mark γ (hreg hγ), F.distinct.mono hreg⟩
  suffices hc : regular.card ≤ b.row.prefixFee + b.row.retained by
    have herase : Γ.card - 1 ≤ regular.card := Finset.pred_card_le_card_erase
    omega
  obtain ⟨H,hH⟩ := P1_7.adjacent_chart (asP1Model M) (asP1Family M G)
  obtain ⟨rows,src⟩ := h1 b u del M regular G hw hshift H hH
  obtain ⟨pairs⟩ := h2 b u del M regular G hw hshift rows src
  obtain ⟨Q⟩ := h3 b u del M regular G hw hshift H hH
    (fun _ => persistent_curve M G hw) rows src pairs
  let keep := regular \ Q.books.union
  have hk : keep ⊆ regular := Finset.sdiff_subset
  have hpaid : (regular \ keep).card ≤ b.row.prefixFee := by
    apply (Finset.card_le_card ?_).trans Q.books.card_union
    intro γ hγ
    obtain ⟨ha,hn⟩ := Finset.mem_sdiff.mp hγ
    by_contra hm
    exact hn (Finset.mem_sdiff.mpr ⟨ha,hm⟩)
  have cover : ∀ γ ∈ keep, ∃ q ∈ Q.parents, MarkOn M G q γ := fun γ hγ =>
    (Q.covers γ (hk hγ)).resolve_left (Finset.mem_sdiff.mp hγ).2
  suffices hkept : keep.card ≤ b.row.retained by
    have hpart := Finset.card_sdiff_add_card_eq_card hk
    omega
  by_cases hm : keep.Nonempty
  · obtain ⟨γ,hγ⟩ := hm
    obtain ⟨q,hq,_⟩ := cover γ hγ
    obtain ⟨f,hf⟩ := K1_14_3_7.proof Q.parents ⟨q,hq⟩ Q.geometric
    have hred : Reduced f := ⟨hf.positive, hf.primitive, hf.separable⟩
    obtain ⟨hl,hu⟩ := window_nat hw
    obtain ⟨i,he,hs⟩ := grade_of_rejections (b := b) hf.positive (by
      intro x hE hv
      have trace := trace_of_full src hw Q.geometric Q.terminal_pass hf x
      exact (h4 b _ hl hu x).not_ge (joint_loss hl hu x hred trace hE hv))
    apply retained_count h5 M G hw hshift hH keep hk f hred i he hs
    intro η hη
    obtain ⟨q',hq',hon⟩ := cover η hη
    have hz := RingHom.mem_ker.mp (hon (hf.vanishes q' hq'))
    simpa only [coe_eval₂RingHom, eval₂_C, atMark] using hz
  · simp [Finset.not_nonempty_iff_eq_empty.mp hm]
end
end P3_7
end
