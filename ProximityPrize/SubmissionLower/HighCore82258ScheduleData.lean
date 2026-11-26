import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.R6960Front6960Rank4
import ProximityPrize.SubmissionLower.HighCore82258PrefixHelpers
import ProximityPrize.SubmissionLower.GoldBranch7N3
set_option Elab.async false




set_option Elab.async false

-- merged module HighCore82268JointRankBase
section Merged_HighCore82268JointRankBase

set_option Elab.async false

namespace HighCore82268JointRank

open Finset
open K1_14_2 (Ambient)
open P1_7_4 (Mass dotQ massQ weightedBill bill_bound)




/-- Linear bound for the nonlinear fixed-jet fee. -/
theorem fixed_fee_linear (L mu tau pivot : ℚ) (hL : 0 ≤ L) (hmu : 0 ≤ mu)
    (htau : 0 ≤ tau) (htau' : tau ≤ 1) {B J Bmax Jmax : ℕ}
    (hJB : J ≤ B) (hB : B ≤ Bmax) (hJ : J ≤ Jmax) :
    let a := mu + 2*L*(B-1 : ℕ)
    let v := min a (L*(2*J-1 : ℕ))
    ((((B-J : ℕ) : ℚ)*v + J*a).ceil.toNat + B^2 : ℕ) ≤
      ((4*L*Bmax*tau+mu-4*L*pivot)*J + (4*L*Jmax*(1-tau)+Bmax)*B+2*L*pivot^2+1 : ℚ) := by
  dsimp only
  let a := mu + 2*L*(B-1 : ℕ)
  let v := min a (L*(2*J-1 : ℕ))
  let q : ℚ := ((B-J : ℕ) : ℚ)*v + J*a
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hv : 0 ≤ v := le_min ha (by positivity)
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hb0 : (0 : ℚ) ≤ B := Nat.cast_nonneg _
  have hj0 : (0 : ℚ) ≤ J := Nat.cast_nonneg _
  have hb : (B : ℚ) ≤ Bmax := by exact_mod_cast hB
  have hj : (J : ℚ) ≤ Jmax := by exact_mod_cast hJ
  have hqceil : 0 ≤ q.ceil := by
    have h : (0 : ℚ) ≤ (q.ceil : ℚ) := hq.trans Rat.le_ceil
    exact_mod_cast h
  have hc : ((q.ceil.toNat : ℕ) : ℚ) ≤ q + 1 := by
    rw [← Int.cast_natCast, Int.toNat_of_nonneg hqceil]
    exact Rat.ceil_lt.le
  have hva : v ≤ 2*L*J := by
    have hd : ((2*J-1 : ℕ) : ℚ) ≤ 2*J := by exact_mod_cast Nat.sub_le (2*J) 1
    exact (min_le_right _ _).trans (by nlinarith only [mul_le_mul_of_nonneg_left hd hL])
  have haa : a ≤ mu + 2*L*B := by
    have hd : ((B-1 : ℕ) : ℚ) ≤ B := by exact_mod_cast Nat.sub_le B 1
    dsimp [a]
    nlinarith only [mul_le_mul_of_nonneg_left hd hL]
  have hfirst : ((B-J : ℕ) : ℚ)*v ≤ ((B : ℚ)-J)*(2*L*J) := by
    rw [Nat.cast_sub hJB]
    exact mul_le_mul_of_nonneg_left hva (sub_nonneg.mpr (by exact_mod_cast hJB))
  have hsecond := mul_le_mul_of_nonneg_left haa hj0
  have hq' : q ≤ 4*L*B*J + mu*J - 2*L*J^2 := by
    dsimp [q]
    linarith only [hfirst,hsecond]
  have hleft := mul_le_mul_of_nonneg_left hb (show 0 ≤ 4*L*tau*J by positivity)
  have hright := mul_le_mul_of_nonneg_left hj
    (show 0 ≤ 4*L*(1-tau)*B by positivity)
  have hsq := mul_le_mul_of_nonneg_left hb hb0
  have htan : -2*L*(J : ℚ)^2 ≤ -4*L*pivot*J + 2*L*pivot^2 := by
    nlinarith only [mul_nonneg hL (sq_nonneg ((J : ℚ)-pivot))]
  change ((q.ceil.toNat + B^2 : ℕ) : ℚ) ≤ _
  push_cast
  nlinarith only [hq', hc, hleft, hright, hsq, htan]

#print axioms fixed_fee_linear

end HighCore82268JointRank

end Merged_HighCore82268JointRankBase

-- merged module HighCore82258ScheduleData
section Merged_HighCore82258ScheduleData

set_option Elab.async false
set_option autoImplicit true
set_option maxRecDepth 18000

set_option Elab.async false
set_option autoImplicit true
open HighCore82258 (start finish  retainedCap)
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



end
end HighCore82258_3
end

namespace HighCore82258JointRank
open HighCore82258 (Band agreement blockLength degreeAt finish gap)
open HighCore82258_3 (rankMass)
open P1_7_4 (Mass)



end HighCore82258JointRank

section
namespace HighCore82258_3
noncomputable section
open HighCore82258 (Band K p agreement AnchorModel AnchoredFamily  degreeAt stages fees fullCutoff terminal curveUnit)
open K1_14 (Shape)
open K1_14_2 (ODE fixedAt)
open K1_14_2_2 (ODECaps)






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

end
end HighCore82258_3
end

end Merged_HighCore82258ScheduleData
