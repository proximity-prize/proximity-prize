import ProximityPrize.SubmissionLower.HighCore82258ScheduleData
import ProximityPrize.SubmissionLower.KoalaH2429LocalData

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 12000000
set_option maxRecDepth 18000

namespace KoalaH2429PrefixNumbers
open P1_7_4 (Mass dotQ running weightedBill)
open HighCore82258 (Band fees stages)
open HighCore82258_3 (initialE initialCap history cutWeight pointLimit)
open HighCore82258JointRank (capB capJ)

inductive FeeGrade
  | base | sixteen | seventeen

def degree : FeeGrade → ℕ
  | .base => 0
  | .sixteen => 16
  | .seventeen => 17

private abbrev band : Band := .h2429
abbrev rho : ℚ := 262144 / 179876
abbrev lambda : ℚ := rho * 128644
abbrev alpha : ℚ := 1 + 2 * lambda
abbrev qField : ℚ := 2130706434

def rate0Table : FeeGrade → List ℚ
  | .base => [249670650, 263491496, 211524978, 192940090, 169844180, 146945269, 129133574, 115232784, 133169153, 113037804, 102467804, 78158855, 80375030, 87283142, 75968746, 89799099, 109319010, 102016226, 135603703, 152023703, 116801772, 163971729]
  | .sixteen => [249339834, 263159320, 211254978, 192640090, 169504180, 146945269, 129133574, 115102784, 133169153, 112867804, 102337804, 78088855, 79585030, 87283142, 74628874, 89799099, 109319010, 99091490, 135603703, 152023703, 110653228, 156956625]
  | .seventeen => [249319158, 263138559, 211254978, 192640090, 169504180, 146945269, 129133574, 115032784, 133169153, 112867804, 102337804, 78088855, 79585030, 87283142, 74545132, 89799099, 109319010, 98908694, 135603703, 152023703, 110268944, 156518181]

def rate1Table : FeeGrade → List ℚ
  | .base => [1397491, 1326396, 1699571, 1883645, 2154590, 2521298, 2897440, 3271718, 2812217, 3344723, 3708744, 4924811, 4777390, 4384741, 5070499, 4262540, 3469065, 3727101, 2760805, 2439971, 3229473, 2248633]
  | .sixteen => [1400111, 1328033, 1701709, 1887129, 2160035, 2521298, 2897440, 3275678, 2812217, 3350407, 3714028, 4929468, 4829941, 4384741, 5160959, 4262540, 3469065, 3845996, 2760805, 2439971, 3424454, 2360974]
  | .seventeen => [1400275, 1328135, 1701709, 1887129, 2160035, 2521298, 2897440, 3278018, 2812217, 3350407, 3714028, 4929468, 4829941, 4384741, 5167370, 4262540, 3469065, 3853426, 2760805, 2439971, 3437303, 2367996]

def rate0 (g : FeeGrade) (i : ℕ) : ℚ := (rate0Table g)[i]?.getD 0
def rate1 (g : FeeGrade) (i : ℕ) : ℚ := (rate1Table g)[i]?.getD 0

def integerHistory (i : ℕ) : Mass :=
  fun k => (⌊history band i k⌋ : ℤ)

def rank : Mass :=
  ![0, 4*lambda*capB band*(49/100) + rho - 4*lambda*14000,
     4*lambda*capJ band*(51/100) + capB band, 0]

def rounding : ℚ := rank 1 + 2*rank 2 + 2*lambda*14000^2 + 1

def seedWeight : ℕ → Mass := cutWeight band 0

def localSupport (i : ℕ) : ℚ :=
  match i with
  | 14 => KoalaH2429LocalSupport.local14.cap
  | 17 => KoalaH2429LocalSupport.local17.cap
  | 20 => KoalaH2429LocalSupport.local20.cap
  | 21 => KoalaH2429LocalSupport.local21.cap
  | _ => dotQ (seedWeight i) (integerHistory i)

def adjustedSeed (g : FeeGrade) : ℚ :=
  weightedBill 22 seedWeight integerHistory - degree g * running seedWeight 22 0

def discountedWeight (g : FeeGrade) (i : ℕ) : Mass :=
  if i = 0 then rank else
    fun k => rate0 g (i-1) * seedWeight (i-1) k +
      rate1 g (i-1) * cutWeight band 1 (i-1) k

def discountedHistory (i : ℕ) : Mass :=
  if i = 0 then integerHistory 0 else integerHistory (i-1)

def loss (g : FeeGrade) : ℚ :=
  weightedBill 23 (discountedWeight g) discountedHistory + adjustedSeed g +
    rounding - degree g * running (discountedWeight g) 23 0

def movingUnit (g : ℕ) : ℚ := alpha * (2*(g : ℚ)-1) + rho

private def fixedFee (B J : ℕ) : ℕ :=
  let ap := rho + 2 * lambda * (B-1 : ℕ)
  let vp := min ap (lambda * (2*J-1 : ℕ))
  (⌈(B-J : ℕ)*vp + J*ap⌉).toNat + B^2

def fixedBankFees : ℕ :=
  ((stages band).map fun s =>
    fixedFee s.free.shape.B s.free.shape.J + fixedFee s.moving.shape.B s.moving.shape.J).sum

/-- Full prefix before the disjoint seed-parent deduction. -/
def fullPrefix (g : FeeGrade) : ℕ :=
  (⌈loss g⌉).toNat + (⌈pointLimit band⌉).toNat + (fees band).lowSeed +
    (fees band).lowJet + fixedBankFees + (fees band).content + 1

def lowSeedSaving : ℕ := (fees band).lowSeed - initialE band

theorem low_seed_exact :
    lowSeedSaving = 1063635867614196 ∧
    (fees band).lowSeed = initialE band + lowSeedSaving ∧
    (2130706434 : ℚ) ≤ rank 2 := by decide +kernel

/-- Use one debit for the loss and seed books, then reserve the erased mark. -/
theorem seed_parent_prefix (g : FeeGrade) {lostAndSeed points lowJet fixed content : ℕ}
    (hlost : lostAndSeed ≤ (⌈loss g⌉).toNat + initialE band)
    (hpoints : points ≤ (⌈pointLimit band⌉).toNat)
    (hjet : lowJet ≤ (fees band).lowJet)
    (hfixed : fixed ≤ fixedBankFees)
    (hcontent : content ≤ (fees band).content) :
    lostAndSeed + points + lowJet + fixed + content + 1 ≤ fullPrefix g - lowSeedSaving := by
  have hfee := low_seed_exact.2.1
  unfold fullPrefix
  omega

theorem rate_checks (g : FeeGrade) (i : Fin 22) :
    qField / 81 ≤ rate0 g i ∧ 0 ≤ rate1 g i ∧
    (∀ j : Fin 81, 0 < j.val →
      max 0 (1-rate0 g i * j.val / qField)*movingUnit j.val≤rate1 g i) ∧
    min (adjustedSeed g) (localSupport i - degree g * seedWeight i 0) ≤ rate0 g i := by
  cases g <;> fin_cases i <;> decide +kernel

theorem fullPrefix_base : fullPrefix .base = 113308639594618063 := by
  decide +kernel

theorem fullPrefix_sixteen : fullPrefix .sixteen = 111200883431942893 := by
  decide +kernel

theorem fullPrefix_seventeen : fullPrefix .seventeen = 111072402022864940 := by
  decide +kernel

end KoalaH2429PrefixNumbers
