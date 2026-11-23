import ProximityPrize.SubmissionLower.KoalaH2429ContactData
-- Ported from public PR657, e07f14a81dfe2cf1bda985e67040ad4d31fe81ab, HighCore82258ScheduleData.lean.
import ProximityPrize.SubmissionLower.HighCore82258Family
import ProximityPrize.SubmissionLower.GoldBranch7N3
import ProximityPrize.SubmissionLower.HighCore82268JointRankBase

set_option Elab.async false
set_option autoImplicit true
set_option maxRecDepth 18000

set_option Elab.async false
set_option autoImplicit true
open HighCore82258 (start finish prefixFee retainedCap)
set_option maxHeartbeats 2000000

open FrontCore82258 (effectiveHeight)

section
namespace HighCore82258_3
noncomputable section
open Polynomial
open HighCore82258 (Band K p agreement blockLength AnchorModel AnchoredFamily)
open HighCore82258 (Stage stages terminal fullCutoff degreeAt gap fees curveUnit)
open K1_14 (Shape Jet Seeds FX Banks atX jetAt seedHasse graphEval)
open K1_14_2 (Ambient ODE OnJet)
open K1_14_2_2 (Active Fits FixedPart ODECaps fixedOn mass sectionDegree weight dot)
open K1_14_2_2_4 (pairCap residualShape highCap highScale)
open scoped BigOperators Classical
export P1_7_4 (Mass massQ dotQ capMin pairMinSeed cornerBound pairedCap PairedMass
  degreeVector introWeight introJump envelope running weightedBill ODEGuard)
def stageAt (b : Band) (i : ℕ) : Stage :=
  ((stages b)[i]?).getD ⟨0,terminal b,terminal b⟩
theorem stage_mem {b : Band} {i : ℕ} (hi : i < (stages b).length) :
    stageAt b i ∈ stages b:=by
  rw [stageAt,List.getElem?_eq_getElem hi]
  exact List.getElem_mem hi
def laterCount (b:Band):=(stages b).length - 1
def introIndices : Band → List ℕ
  | .h2367 => [1,2,3,4,5,6,7,8,9,11,12,13,14]
  | .h2430 | .h2429 | .h2429B => [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 13, 14]
def stopIndex (_:Band):ℕ:=0
def introAccount (b : Band) (k : Fin 4) :
    List ℕ→(Fin 3→ℕ)→(Fin 3→ℕ)→ℕ
  | [], cap, old =>
    introJump cap old (stageAt b 0).moving.shape k +
      (![cap 0,cap 2,2*cap 0*cap 2,cap 2*cap 2]:Fin 4→ℕ) k
  | i :: is, cap, old =>
    let s:=stageAt b i
    let c:=s.free.shape
    introJump cap old c k + introAccount b k is
      (fun j => min (cap j) (degreeVector c j / (s.reserve+1)))
      (fun j => max (old j) (introWeight c k j))
def initialCap (b : Band) (k : Fin 4) : ℕ :=
  let s:=stageAt b 0
  if (introIndices b).isEmpty then
    (cornerBound s.free.shape s.moving.shape 1 1 false k).floor.toNat
  else introAccount b k (introIndices b) (degreeVector s.free.shape) (fun _ => 0)
def initialE (b : Band) : ℕ :=
  if (introIndices b).isEmpty then
    let s:=stageAt b 0
    s.free.shape.U*s.moving.shape.U+(pairMinSeed s.free.shape s.moving.shape)^2
  else initialCap b 3
def mixedCapTable : Band → List (Option ℚ)
  | .h2367 => [none,none,none,none,none,none,none,none,none,none,none,none,none,none,some (72953035/1458),some (16119743/363),some (74375512/1849),some (5349235/144),some (4108008034/18225),some (4591282259/127008),some (90268456/2523),some (22873370532/45125)]
  | .h2430 | .h2429 | .h2429B => []
def mixedCap (b:Band) (i:ℕ):Option ℚ:=((mixedCapTable b)[i]?).getD none

/-- The certified four coordinate caps at positive H2430 stages. -/
def contactCap : Band → ℕ → Option Mass
  | .h2367, _ => none
  | .h2430, i => ([none, some ![(12345/2),(620617/4),(2899455/4),(23854293/4)], some ![(33224/9),(717662/9),(3310781/9),(8098750/3)], some ![(8473/4),56403,(4193081/16),2055366], some ![(39909/25),(1070467/25),(5124231/25),(36408528/25)], some ![(53009/36),(279730/9),(461152/3),(4007993/4)], some ![(32709/32),(753249/32),(5707540/49),(23235141/32)], some ![(90802/121),(180794/11),86131,(29350517/50)], some ![(131620/289),(3516260/289),(6766989/98),(534077049/784)], some ![(9974/11),(210032/11),(5023403/50),(50806434/121)], some ![(219077/324),(336719/27),(2450465/36),(160044589/576)], some ![(3432/7),(1486606/147),(401047551/7225),(70524897/200)], some ![(270609/784),(3728187/392),(1348987642/25921),(330392808/625)], some ![(140093/512),(11149761/1024),(80370145/1352),(165719529/196)], some ![(405580/729),(2534021/243),(1185446/21),(21264653/96)], some ![(130301/361),(5747347/722),(44045177/1024),(2973626443/10404)], some ![(35059/100),(52554536/7203),(722971935/18491),(26037952798/99225)], some ![(633047/1922),(27438205/3969),(187445425/5096),(700143777/2800)], some ![(238987/1156),(700928022/22445),(504496409/2156),(331278261449/34225)], some ![(517732/1681),(215886199/32805),(48266417639/1375929),(6003685367/24642)], some ![(6550097/21160),(33856343/5290),(10294331317/296450),(78525141013/337561)], some ![(155619/841),(247672732/3481),(257704690693/451250),(47129300981297/984064)]] : List (Option Mass))[i]?.getD none
  | .h2429, i | .h2429B, i => if h : 0 < i ∧ i < 22 then
      some (KoalaH2429Contact.contact ⟨i-1, by omega⟩).cap
    else none

def stageCap (b : Band) (i : ℕ) (square : Bool) : Mass :=
  let s:=stageAt b i
  fun k =>
    let raw:=pairedCap s.free.shape s.moving.shape s.reserve square k
    match (if square then contactCap b i else none) with
    | some c => c k
    | none =>
      if square = true ∧ k = 2 then
        match mixedCap b i with
        | none => raw
        | some c => min raw c
      else raw
def history (b : Band) : ℕ → Mass
  | 0 => fun k => initialCap b k
  | i+1 => capMin (history b i) (stageCap b (i+1) (decide (stopIndex b≤ i+1)))
def rankMass (b : Band) : Mass :=
  if stopIndex b=0 then history b 0
  else capMin (history b (stopIndex b - 1)) (stageCap b (stopIndex b) false)
def rankB (b:Band):ℕ:=(rankMass b 2).floor.toNat
def rankJ (b:Band):ℕ:=(rankMass b 1).floor.toNat
def cutShape (b : Band) (i : ℕ) : Shape :=
  if i < laterCount b then envelope (stageAt b (i+1)) else (terminal b).shape
def cutWeight (b : Band) (fee : Fin 3) (i : ℕ) : Mass :=
  fun k => weight (cutShape b i) fee k
def seedLimit (b : Band) : ℚ :=
  weightedBill (laterCount b+1) (cutWeight b 0) (history b)
def pointLimit (b : Band) : ℚ :=
  dotQ (running (cutWeight b 2) (laterCount b + 1))
    ![(initialCap b 0:ℚ),(initialCap b 1:ℚ),(initialCap b 2:ℚ),(initialE b:ℚ)]
def lossWeight (b : Band) (a h : ℕ → ℚ) (i : ℕ) : Mass :=
  fun k => a i*cutWeight b 0 i k+h i*cutWeight b 1 i k
def fixedFee (hi B J : ℕ) : ℕ :=
  let d:=degreeAt hi
  let q:=gap hi
  let lam:ℚ:=(blockLength:ℚ) / agreement
  let mu:ℚ:=((blockLength-d:ℕ):ℚ) / q
  let ap:=mu+2*lam*d*(B-1:ℕ)
  let vp:=min ap (lam*d*(2*J-1:ℕ))
  (((B-J:ℕ):ℚ)*vp+J*ap).ceil.toNat+B^2
def jointRank (_:Band):Bool:=true

theorem jointRank_start (b : Band) (h : jointRank b = true) : start b < 7773 := by
  cases b <;> decide

def rankTau (_:Band):ℚ:=(49/100)
def rankPivot : Band → ℚ
  | .h2367 => 14700
  | .h2430 | .h2429 | .h2429B => 14000

end
end HighCore82258_3
end

namespace HighCore82258JointRank
open HighCore82258 (Band agreement blockLength degreeAt finish gap)
open HighCore82258_3 (rankMass)
open P1_7_4 (Mass)
def lambdaDegree (b:Band):ℚ:=(blockLength:ℚ) / agreement*degreeAt (finish b)
def mu (b:Band):ℚ:=((blockLength-degreeAt (finish b):ℕ):ℚ) / gap (finish b)
def capB (b:Band):ℕ:=(rankMass b 2).floor.toNat+2
def capJ (b:Band):ℕ:=(rankMass b 1).floor.toNat+1

def rankCharge (b : Band) (tau pivot : ℚ) : Mass :=
  ![0, 4*lambdaDegree b*capB b*tau+mu b-4*lambdaDegree b*pivot,
    4*lambdaDegree b*capJ b*(1-tau)+capB b,0]

def rankRounding (b : Band) (tau pivot : ℚ) : ℚ :=
  rankCharge b tau pivot 1+2*rankCharge b tau pivot 2+2*lambdaDegree b*pivot^2+1

end HighCore82258JointRank

section
namespace HighCore82258_3
noncomputable section
open HighCore82258 (Band K p agreement AnchorModel AnchoredFamily InBand degreeAt stages fees fullCutoff terminal curveUnit gradedLoss)
open K1_14 (Shape)
open K1_14_2 (ODE fixedAt)
open K1_14_2_2 (ODECaps)
open HighCore82268JointRank (splice)
open HighCore82258JointRank (rankCharge rankRounding)

def lossCount (b:Band):ℕ:=laterCount b+1+(if jointRank b then 1 else 0)

def lossWeights (b : Band) (a h : ℕ → ℚ) : ℕ → Mass :=
  if jointRank b then splice (stopIndex b) (rankCharge b (rankTau b) (rankPivot b)) (lossWeight b a h)
  else lossWeight b a h

def lossHistory (b : Band) : ℕ → Mass :=
  if jointRank b then splice (stopIndex b) (rankMass b) (history b) else history b

def lossOffset (b : Band) : ℚ :=
  if jointRank b then rankRounding b (rankTau b) (rankPivot b) else 0

def FixedCount : Prop :=
  ∀ (b : Band) u del (M : AnchorModel u del) Γ (F : AnchoredFamily M Γ),
    InBand b (effectiveHeight M) → ∀ B J:ℕ,ODEGuard B J →
    ∀ G:ODE,ODECaps G B J → ∀ T ⊆ Γ,
    (∀ γ ∈ T,fixedAt G (F.scalar γ)=0)→T.card≤fixedFee (finish b) B J

def fixedBudget (b : Band) : ℕ :=
  let price (s:Shape):=fixedFee (finish b) s.B s.J
  ∑ i ∈ Finset.range (stages b).length,
    (price (stageAt b i).free.shape+price (stageAt b i).moving.shape)
structure BankGuard (hi reserve : ℕ) (s : Shape) : Prop where
  ode:ODEGuard s.B s.J
  seed_small:s.U < p
  pos:0 < s.m*agreement
  buffer:2*hi*reserve≤fullCutoff s
structure ScheduleOK (b : Band) : Prop where
  stages_pos:0 < (stages b).length
  zero:(stageAt b 0).reserve=0
  later_pos : ∀ i < laterCount b,0 < (stageAt b (i+1)).reserve
  small_reserve : ∀ i < (stages b).length,(stageAt b i).reserve < p
  stop_le:stopIndex b≤laterCount b
  intro_pos : ∀ i ∈ introIndices b,0 < i ∧ i < (stages b).length
  intro_asc:(introIndices b).Pairwise (· < ·)
  stage_guard : ∀ i < (stages b).length,
    let s:=stageAt b i
    BankGuard (finish b) s.reserve s.free.shape ∧ BankGuard (finish b) s.reserve s.moving.shape
  terminal_guard:BankGuard (finish b) 0 (terminal b).shape
  initial_small : ∀ k,initialCap b k < p
  initial_e_ge:initialCap b 3≤ initialE b
  content_small:(stageAt b 0).free.shape.U+(stageAt b 0).moving.shape.U < p
  rank_guard:ODEGuard (rankB b) (rankJ b)
  low_seed:(p+1)*initialCap b 2+initialE b≤(fees b).lowSeed
  low_jet:initialCap b 0+(if jointRank b then 0 else fixedFee (finish b) (rankB b) (rankJ b))≤(fees b).lowJet
  fixed:fixedBudget b≤(fees b).fixedODE
  content:(p+1)*((stageAt b 0).free.shape.U+(stageAt b 0).moving.shape.U)≤(fees b).content
structure RateOK (hi : ℕ) (a h : ℚ) : Prop where
  degree:((p+1:ℕ):ℚ) / 81≤a
  height:0≤h
  interpolation : ∀ g : ℕ, 0 < g → g ≤ 80 →
    max 0 (1 - a*g/((p+1:ℕ):ℚ))*curveUnit hi g≤h
structure LossLedger (b : Band) : Prop where
  seed_small:seedLimit b < (p:ℚ)
  points:pointLimit b≤((fees b).point:ℚ)
  discount : (start b) < 7773 →
    ∃ a h : ℕ → ℚ,
      (∀ i ≤ laterCount b, RateOK (finish b) (a i) (h i) ∧
        min (seedLimit b) (dotQ (cutWeight b 0 i) (history b i))≤a i) ∧
      weightedBill (lossCount b) (lossWeights b a h) (lossHistory b) + seedLimit b + lossOffset b ≤
        ((fees b).loss:ℚ)
  rank_guard : jointRank b = true →
    0 ≤ rankTau b ∧ rankTau b ≤ 1 ∧ 0 ≤ rankCharge b (rankTau b) (rankPivot b) 1 ∧
      (rankMass b 2).floor.toNat+2 < p
  direct:7773≤(start b)→((p+1:ℕ):ℚ)*seedLimit b≤((fees b).loss:ℚ)

def chargeDegree (e:ℕ):ℕ:=if e=16 ∨ e=17 then e else 0

theorem chargeDegree_le (e : ℕ) : chargeDegree e ≤ e := by
  unfold chargeDegree
  split <;> omega

def seedCredit (b:Band):ℚ:=P1_7_4.running (cutWeight b 0) (laterCount b+1) 0

def mixedCredit (b : Band) (a h : ℕ → ℚ) : ℚ :=
  P1_7_4.running (lossWeights b a h) (lossCount b) 0

def adjustedSeed (b:Band) (e:ℕ):ℚ:=seedLimit b - seedCredit b*chargeDegree e

def adjustedLocal (b : Band) (e i : ℕ) : ℚ :=
  dotQ (cutWeight b 0 i) (history b i) - cutWeight b 0 i 0*chargeDegree e

structure GradedLedger (b : Band) : Prop where
  seed_small : ∀ e,adjustedSeed b e < (p:ℚ)
  points:pointLimit b≤((fees b).point:ℚ)
  discount : ∀ e, ∃ a h : ℕ → ℚ,
    (∀ i ≤ laterCount b, RateOK (finish b) (a i) (h i) ∧
      min (adjustedSeed b e) (adjustedLocal b e i)≤a i) ∧
    weightedBill (lossCount b) (lossWeights b a h) (lossHistory b) +
      adjustedSeed b e+lossOffset b - mixedCredit b a h*chargeDegree e≤gradedLoss b e
  rank_guard : jointRank b = true →
    0 ≤ rankTau b ∧ rankTau b ≤ 1 ∧ 0 ≤ rankCharge b (rankTau b) (rankPivot b) 1 ∧
      (rankMass b 2).floor.toNat+2 < p


end
end HighCore82258_3
end
