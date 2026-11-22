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
  ((stages b)[i]?).getD ⟨0, terminal b, terminal b⟩
theorem stage_mem {b : Band} {i : ℕ} (hi : i < (stages b).length) :
    stageAt b i ∈ stages b := by
  rw [stageAt, List.getElem?_eq_getElem hi]
  exact List.getElem_mem hi
def laterCount (b : Band) := (stages b).length - 1
def introIndices : Band → List ℕ
  | .h2367 => [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]
  | .h2395 => [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]
  | .h7773 => []
def stopIndex (_ : Band) : ℕ := 0
def introAccount (b : Band) (k : Fin 4) :
    List ℕ → (Fin 3 → ℕ) → (Fin 3 → ℕ) → ℕ
  | [], cap, old =>
    introJump cap old (stageAt b 0).moving.shape k +
      (![cap 0, cap 2, 2*cap 0*cap 2, cap 2 * cap 2] : Fin 4 → ℕ) k
  | i :: is, cap, old =>
    let s := stageAt b i
    let c := s.free.shape
    introJump cap old c k + introAccount b k is
      (fun j => min (cap j) (degreeVector c j / (s.reserve+1)))
      (fun j => max (old j) (introWeight c k j))
def initialCap (b : Band) (k : Fin 4) : ℕ :=
  let s := stageAt b 0
  if (introIndices b).isEmpty then
    (cornerBound s.free.shape s.moving.shape 1 1 false k).floor.toNat
  else introAccount b k (introIndices b) (degreeVector s.free.shape) (fun _ => 0)
def initialE (b : Band) : ℕ :=
  if (introIndices b).isEmpty then
    let s := stageAt b 0
    s.free.shape.U * s.moving.shape.U + (pairMinSeed s.free.shape s.moving.shape)^2
  else initialCap b 3
def stageCap (b : Band) (i : ℕ) (square : Bool) : Mass :=
  let s := stageAt b i
  pairedCap s.free.shape s.moving.shape s.reserve square
def history (b : Band) : ℕ → Mass
  | 0 => fun k => initialCap b k
  | i+1 => capMin (history b i) (stageCap b (i+1) (decide (stopIndex b ≤ i+1)))
def rankMass (b : Band) : Mass :=
  if stopIndex b = 0 then history b 0
  else capMin (history b (stopIndex b - 1)) (stageCap b (stopIndex b) false)
def rankB (b : Band) : ℕ := (rankMass b 2).floor.toNat
def rankJ (b : Band) : ℕ := (rankMass b 1).floor.toNat
def cutShape (b : Band) (i : ℕ) : Shape :=
  if i < laterCount b then envelope (stageAt b (i+1)) else (terminal b).shape
def cutWeight (b : Band) (fee : Fin 3) (i : ℕ) : Mass :=
  fun k => weight (cutShape b i) fee k
def seedLimit (b : Band) : ℚ :=
  weightedBill (laterCount b+1) (cutWeight b 0) (history b)
def pointLimit (b : Band) : ℚ :=
  dotQ (running (cutWeight b 2) (laterCount b + 1))
    ![(initialCap b 0 : ℚ), (initialCap b 1 : ℚ), (initialCap b 2 : ℚ), (initialE b : ℚ)]
def lossWeight (b : Band) (a h : ℕ → ℚ) (i : ℕ) : Mass :=
  fun k => a i * cutWeight b 0 i k + h i * cutWeight b 1 i k
def fixedFee (hi B J : ℕ) : ℕ :=
  let d := degreeAt hi
  let q := gap hi
  let lam : ℚ := (blockLength : ℚ) / agreement
  let mu : ℚ := ((blockLength-d : ℕ) : ℚ) / q
  let ap := mu + 2*lam*d*(B-1 : ℕ)
  let vp := min ap (lam*d*(2*J-1 : ℕ))
  (((B-J : ℕ) : ℚ)*vp + J*ap).ceil.toNat+B^2
def jointRank : Band → Bool
  | .h2367 => true
  | _ => false

theorem jointRank_start (b : Band) (h : jointRank b = true) : start b < 7773 := by
  cases b <;> simp [jointRank] at h
  decide

def rankTau (_ : Band) : ℚ := (49/100)
def rankPivot (_ : Band) : ℚ := (47843/5)

end
end HighCore82258_3
end

namespace HighCore82258JointRank
open HighCore82258 (Band agreement blockLength degreeAt finish gap)
open HighCore82258_3 (rankMass)
open P1_7_4 (Mass)
def lambdaDegree (b : Band) : ℚ := (blockLength : ℚ) / agreement * degreeAt (finish b)
def mu (b : Band) : ℚ := ((blockLength-degreeAt (finish b) : ℕ) : ℚ) / gap (finish b)
def capB (b : Band) : ℕ := (rankMass b 2).floor.toNat+2
def capJ (b : Band) : ℕ := (rankMass b 1).floor.toNat+1

def rankCharge (b : Band) (tau pivot : ℚ) : Mass :=
  ![0, 4*lambdaDegree b*capB b*tau+mu b-4*lambdaDegree b*pivot,
    4*lambdaDegree b*capJ b*(1-tau)+capB b, 0]

def rankRounding (b : Band) (tau pivot : ℚ) : ℚ :=
  rankCharge b tau pivot 1 + 2*rankCharge b tau pivot 2 + 2*lambdaDegree b*pivot^2 + 1

end HighCore82258JointRank

section
namespace HighCore82258_3
noncomputable section
open HighCore82258 (Band K p agreement AnchorModel AnchoredFamily InBand degreeAt stages fees fullCutoff terminal curveUnit)
open K1_14 (Shape)
open K1_14_2 (ODE fixedAt)
open K1_14_2_2 (ODECaps)
open HighCore82268JointRank (splice)
open HighCore82258JointRank (rankCharge rankRounding)

def lossCount (b : Band) : ℕ := laterCount b + 1 + (if jointRank b then 1 else 0)

def lossWeights (b : Band) (a h : ℕ → ℚ) : ℕ → Mass :=
  if jointRank b then splice (stopIndex b) (rankCharge b (rankTau b) (rankPivot b)) (lossWeight b a h)
  else lossWeight b a h

def lossHistory (b : Band) : ℕ → Mass :=
  if jointRank b then splice (stopIndex b) (rankMass b) (history b) else history b

def lossOffset (b : Band) : ℚ :=
  if jointRank b then rankRounding b (rankTau b) (rankPivot b) else 0

def FixedCount : Prop :=
  ∀ (b : Band) u del (M : AnchorModel u del) Γ (F : AnchoredFamily M Γ),
    InBand b M.overhead → ∀ B J : ℕ, ODEGuard B J →
    ∀ G : ODE, ODECaps G B J → ∀ T ⊆ Γ,
    (∀ γ ∈ T, fixedAt G (F.scalar γ) = 0) → T.card ≤ fixedFee (finish b) B J

def fixedBudget (b : Band) : ℕ :=
  let price (s : Shape) := fixedFee (finish b) s.B s.J
  ∑ i ∈ Finset.range (stages b).length,
    (price (stageAt b i).free.shape + price (stageAt b i).moving.shape)
structure BankGuard (hi reserve : ℕ) (s : Shape) : Prop where
  ode : ODEGuard s.B s.J
  seed_small : s.U < p
  pos : 0 < s.m * agreement
  buffer : 2*hi*reserve ≤ fullCutoff s
structure ScheduleOK (b : Band) : Prop where
  stages_pos : 0 < (stages b).length
  zero : (stageAt b 0).reserve = 0
  later_pos : ∀ i < laterCount b, 0 < (stageAt b (i+1)).reserve
  small_reserve : ∀ i < (stages b).length, (stageAt b i).reserve < p
  stop_le : stopIndex b ≤ laterCount b
  intro_pos : ∀ i ∈ introIndices b, 0 < i ∧ i < (stages b).length
  intro_asc : (introIndices b).Pairwise (· < ·)
  stage_guard : ∀ i < (stages b).length,
    let s := stageAt b i
    BankGuard (finish b) s.reserve s.free.shape ∧ BankGuard (finish b) s.reserve s.moving.shape
  terminal_guard : BankGuard (finish b) 0 (terminal b).shape
  initial_small : ∀ k, initialCap b k < p
  initial_e_ge : initialCap b 3 ≤ initialE b
  content_small : (stageAt b 0).free.shape.U + (stageAt b 0).moving.shape.U < p
  rank_guard : ODEGuard (rankB b) (rankJ b)
  low_seed : (p+1)*initialCap b 2 + initialE b ≤ (fees b).lowSeed
  low_jet : initialCap b 0 + (if jointRank b then 0 else fixedFee (finish b) (rankB b) (rankJ b)) ≤ (fees b).lowJet
  fixed : fixedBudget b ≤ (fees b).fixedODE
  content : (p+1)*((stageAt b 0).free.shape.U + (stageAt b 0).moving.shape.U) ≤ (fees b).content
structure RateOK (hi : ℕ) (a h : ℚ) : Prop where
  degree : ((p+1 : ℕ) : ℚ) / 81 ≤ a
  height : 0 ≤ h
  interpolation : ∀ g : ℕ, 0 < g → g ≤ 80 →
    max 0 (1 - a*g/((p+1 : ℕ) : ℚ)) * curveUnit hi g ≤ h
structure LossLedger (b : Band) : Prop where
  seed_small : seedLimit b < (p : ℚ)
  points : pointLimit b ≤ ((fees b).point : ℚ)
  discount : (start b) < 7773 →
    ∃ a h : ℕ → ℚ,
      (∀ i ≤ laterCount b, RateOK (finish b) (a i) (h i) ∧
        min (seedLimit b) (dotQ (cutWeight b 0 i) (history b i)) ≤ a i) ∧
      weightedBill (lossCount b) (lossWeights b a h) (lossHistory b) + seedLimit b + lossOffset b ≤
        ((fees b).loss : ℚ)
  rank_guard : jointRank b = true →
    0 ≤ rankTau b ∧ rankTau b ≤ 1 ∧ 0 ≤ rankCharge b (rankTau b) (rankPivot b) 1 ∧
      (rankMass b 2).floor.toNat + 2 < p
  direct : 7773 ≤ (start b) → ((p+1 : ℕ) : ℚ) * seedLimit b ≤ ((fees b).loss : ℚ)

end
end HighCore82258_3
end
