import ProximityPrize.SubmissionLower.MergedInfra6815_10
import ProximityPrize.SubmissionLower.MergedInfra6815_12
import ProximityPrize.SubmissionLower.MergedInfra6815_7
import ProximityPrize.SubmissionLower.LowerGeometry
import ProximityPrize.SubmissionLower.MergedInfra6815_8
set_option Elab.async false
section MergedPart0
namespace ProximityPrize.SubmissionLower.Lower80899.PhaseRows
open RCN095 LocatorFactorAggregate LocatorArbitraryPowerAvoidance
open LocatorPhase6800Oracle (Potential BaseRow BaseSegment evalBaseSegments rawFlag rawFlag_total rawFlag_middle rawFlag_all)
open Lower80899.Oracle
open LocatorPhase6800Audit (powerBandBudget_mono_fuel)
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
theorem routeable_raw_mono_z
    (s : SourceNumbers) {r v z₁ z₂ : ℕ}
    (hz : z₁ ≤ z₂) (hcap : r + v + z₂ ≤ s.totalCap)
    (hroute : s.Routeable (rawFlag r v z₁)) :
    s.Routeable (rawFlag r v z₂) := by
  rcases hroute with ⟨hr, ht, hy, hs, hband⟩
  have hr' : 1 ≤ r := by simpa only [rawFlag_all] using hr
  have htotal : r + v + z₁ ≤ r + v + z₂ := by omega
  have hpos : 0 < r + v + z₁ := by omega
  have hdiv : s.totalCap / (r + v + z₂) ≤
      s.totalCap / (r + v + z₁) :=
    Nat.div_le_div_left htotal hpos
  have hfuel : s.fuel (rawFlag r v z₂) ≤
      s.fuel (rawFlag r v z₁) := by
    unfold SourceNumbers.fuel
    simp only [rawFlag_total, rawFlag_middle, rawFlag_all]
    exact min_le_min hdiv (le_refl _)
  have hbox : s.totalCap - (r + v + z₂) ≤
      s.totalCap - (r + v + z₁) := Nat.sub_le_sub_left htotal _
  have hsameFuel :
      powerBandBudget 50175 (r + v + z₂) (r + v) r
          (s.totalCap - (r + v + z₂)) (s.middleCap - (r + v))
          (s.slopeCap - r) (s.fuel (rawFlag r v z₂)) ≤
        powerBandBudget 50175 (r + v + z₁) (r + v) r
          (s.totalCap - (r + v + z₁)) (s.middleCap - (r + v))
          (s.slopeCap - r) (s.fuel (rawFlag r v z₂)) := by
    exact powerBandBudget_mono 50175
      (r + v + z₂) (r + v) r
      (s.totalCap - (r + v + z₂)) (s.middleCap - (r + v))
      (s.slopeCap - r)
      (r + v + z₁) (r + v) r
      (s.totalCap - (r + v + z₁)) (s.middleCap - (r + v))
      (s.slopeCap - r) (s.fuel (rawFlag r v z₂))
      hbox (le_refl _) (le_refl _) htotal (le_refl _) (le_refl _)
  have hmoreFuel :
      powerBandBudget 50175 (r + v + z₁) (r + v) r
          (s.totalCap - (r + v + z₁)) (s.middleCap - (r + v))
          (s.slopeCap - r) (s.fuel (rawFlag r v z₂)) ≤
        powerBandBudget 50175 (r + v + z₁) (r + v) r
          (s.totalCap - (r + v + z₁)) (s.middleCap - (r + v))
          (s.slopeCap - r) (s.fuel (rawFlag r v z₁)) :=
    powerBandBudget_mono_fuel 50175 (r + v + z₁) (r + v) r
      (s.totalCap - (r + v + z₁)) (s.middleCap - (r + v))
      (s.slopeCap - r) hfuel
  refine ⟨hr, ?_, ?_, ?_, ?_⟩
  · simpa only [rawFlag_total] using hcap
  · simpa only [rawFlag_middle] using hy
  · simpa only [rawFlag_all] using hs
  · rcases hband with hband | hthin
    · left
      unfold SourceNumbers.band at hband ⊢
      simp only [rawFlag_total, rawFlag_middle, rawFlag_all] at hband ⊢
      exact (hsameFuel.trans hmoreFuel).trans_lt hband
    · right
      have hsameFuelT :
          powerBandBudgetThin 131071 (s.contactCap (rawFlag r v z₂)) 50175
              (contactDec (rawFlag r v z₂)) (r + v + z₂) (r + v) r
              (s.totalCap - (r + v + z₂)) (s.middleCap - (r + v))
              (s.slopeCap - r) (s.fuel (rawFlag r v z₂)) ≤
            powerBandBudgetThin 131071 (s.contactCap (rawFlag r v z₁)) 50175
              (contactDec (rawFlag r v z₁)) (r + v + z₁) (r + v) r
              (s.totalCap - (r + v + z₁)) (s.middleCap - (r + v))
              (s.slopeCap - r) (s.fuel (rawFlag r v z₂)) := by
        have hcap : s.contactCap (rawFlag r v z₂) = s.contactCap (rawFlag r v z₁) := by
          simp only [SourceNumbers.contactCap, contactDec, rawFlag_middle, rawFlag_all]
        have hdec : contactDec (rawFlag r v z₂) = contactDec (rawFlag r v z₁) := by
          simp only [contactDec, rawFlag_middle, rawFlag_all]
        rw [hcap, hdec]
        exact powerBandBudgetThin_mono 131071 50175 (s.fuel (rawFlag r v z₂))
          (s.contactCap (rawFlag r v z₁)) (contactDec (rawFlag r v z₁))
          (r + v + z₂) (r + v) r
          (s.totalCap - (r + v + z₂)) (s.middleCap - (r + v)) (s.slopeCap - r)
          (s.contactCap (rawFlag r v z₁)) (contactDec (rawFlag r v z₁))
          (r + v + z₁) (r + v) r
          (s.totalCap - (r + v + z₁)) (s.middleCap - (r + v)) (s.slopeCap - r)
          le_rfl le_rfl hbox le_rfl le_rfl htotal le_rfl le_rfl
      have hmoreFuelT :
          powerBandBudgetThin 131071 (s.contactCap (rawFlag r v z₁)) 50175
              (contactDec (rawFlag r v z₁)) (r + v + z₁) (r + v) r
              (s.totalCap - (r + v + z₁)) (s.middleCap - (r + v))
              (s.slopeCap - r) (s.fuel (rawFlag r v z₂)) ≤
            powerBandBudgetThin 131071 (s.contactCap (rawFlag r v z₁)) 50175
              (contactDec (rawFlag r v z₁)) (r + v + z₁) (r + v) r
              (s.totalCap - (r + v + z₁)) (s.middleCap - (r + v))
              (s.slopeCap - r) (s.fuel (rawFlag r v z₁)) :=
        powerBandBudgetThin_mono_fuel 131071 (s.contactCap (rawFlag r v z₁)) 50175
          (contactDec (rawFlag r v z₁)) (r + v + z₁) (r + v) r
          (s.totalCap - (r + v + z₁)) (s.middleCap - (r + v)) (s.slopeCap - r) hfuel
      unfold SourceNumbers.bandThin at hthin ⊢
      simp only [rawFlag_total, rawFlag_middle, rawFlag_all] at hthin ⊢
      exact (hsameFuelT.trans hmoreFuelT).trans_lt hthin

def phasePotential : ℕ → Potential
  | 0 => Lower80899.SourceSound.Phase00.potential
  | 1 => Lower80899.SourceSound.Phase01.potential
  | 2 => Lower80899.SourceSound.Phase02.potential
  | 3 => Lower80899.SourceSound.Phase03.potential
  | 4 => Lower80899.SourceSound.Phase04.potential
  | 5 => Lower80899.SourceSound.Phase05.potential
  | 6 => Lower80899.SourceSound.Phase06.potential
  | 7 => Lower80899.SourceSound.Phase03.potential
  | 8 => Lower80899.SourceSound.Phase04.potential
  | _ => Lower80899.SourceSound.PhaseFinal.potential

def thresholdAt (q : Array ℕ) (j : ℕ) : ℕ := (q[j]?).getD 11193
def cachedPrefixAt (q : Array ℕ) (j : ℕ) : ℕ := (q[j]?).getD 0
structure PhaseRowContext where
  R : ℕ
  V : ℕ
  base : BaseRow
  threshold : Array ℕ
  here : Array ℕ
  parent : Array ℕ

def baseAt (c : PhaseRowContext) (z : ℕ) : ℕ := c.base.evalAt z

def parentCharge (c : PhaseRowContext) (phase z : ℕ) : ℕ :=
  (phasePotential phase).eval (rawFlag c.R c.V z) + cachedPrefixAt c.parent phase

def hereCharge (c : PhaseRowContext) (phase z : ℕ) : ℕ :=
  (phasePotential phase).eval (rawFlag c.R c.V z) + cachedPrefixAt c.here phase

def sourceLine (c : PhaseRowContext) : ℕ → ℕ → ℕ
  | 0, z => baseAt c z
  | j + 1, z => parentCharge c j z

def SourceActive (c : PhaseRowContext) : ℕ → ℕ → Prop
  | 0, _ => True
  | j + 1, z => thresholdAt c.threshold j ≤ z

instance (c : PhaseRowContext) (w z : ℕ) : Decidable (SourceActive c w z) := by
  cases w <;> simp only [SourceActive] <;> infer_instance

open SecondJetRowIntervals

def SourceCell (c : PhaseRowContext) : ℕ → ℕ → ℕ → Prop
  | 0, lo, hi => BaseCell c.base lo hi
  | _+1, _, _ => True
instance (c : PhaseRowContext) (w lo hi : ℕ) : Decidable (SourceCell c w lo hi) := by
  cases w <;> simp only [SourceCell] <;> infer_instance

def RunValid (c : PhaseRowContext) (phase start : ℕ) (run : PhaseRun) : Prop :=
  let hi := run.stop - 1
  start < run.stop ∧ run.witness ≤ phase ∧
    SourceActive c run.witness start ∧
    SourceCell c run.witness start hi ∧
    sourceLine c run.witness start ≤ hereCharge c phase start ∧
    sourceLine c run.witness hi ≤ hereCharge c phase hi

instance (c : PhaseRowContext) (phase start : ℕ) (run : PhaseRun) :
    Decidable (RunValid c phase start run) := by
  unfold RunValid
  infer_instance

def RunsValid (c : PhaseRowContext) (phase finish : ℕ) :
    ℕ → List PhaseRun → Prop
  | start, [] => start = finish
  | start, run :: runs =>
      run.stop ≤ finish ∧ RunValid c phase start run ∧
        RunsValid c phase finish run.stop runs

instance (c : PhaseRowContext) (phase finish start : ℕ)
    (runs : List PhaseRun) : Decidable (RunsValid c phase finish start runs) := by
  induction runs generalizing start with
  | nil => simp only [RunsValid]; infer_instance
  | cons run runs ih => simp only [RunsValid]; infer_instance

def phaseFinish (c : PhaseRowContext) (phase : ℕ) : ℕ :=
  min (thresholdAt c.threshold phase) (11193 - (c.R + c.V))

def RowRunsValid (c : PhaseRowContext) (runs : Array (List PhaseRun)) : Prop :=
  ∀ j ∈ List.range 10, RunsValid c j (phaseFinish c j) 0 ((runs[j]?).getD [])

instance (c : PhaseRowContext) (runs : Array (List PhaseRun)) :
    Decidable (RowRunsValid c runs) := by
  unfold RowRunsValid
  infer_instance

end ProximityPrize.SubmissionLower.Lower80899.PhaseRows

namespace ProximityPrize.SubmissionLower.Lower80899.ThresholdFast

open scoped BigOperators
open LocatorLowQuotient

set_option autoImplicit false
set_option maxRecDepth 100000

theorem term_eq (B x : ℕ) :
    (x + 1) * (B + x) - (x + 1) * x / 2 =
      (x + 1) * B + (x + 1).choose 2 := by
  rw [Nat.choose_two_right]
  simp only [Nat.add_sub_cancel]
  have hdvd : 2 ∣ (x + 1) * x := by
    simpa [Nat.mul_comm, Nat.add_comm] using
      (even_iff_two_dvd.mp (Nat.even_mul_succ_self x))
  have hhalf := Nat.div_mul_cancel hdvd
  rw [Nat.mul_add]
  omega

theorem kernelSumRange_succ_all : ∀ n : ℕ,
    kernelSumRange (fun x => x + 1) n = (n + 1).choose 2
  | 0 => by decide
  | n + 1 => by
      rw [LocatorLowQuotient.kernelSumRange_succ, kernelSumRange_succ_all]
      simpa [Nat.choose_one_right, Nat.add_comm, Nat.add_left_comm,
        Nat.add_assoc] using (Nat.choose_succ_succ (n + 1) 1).symm

theorem kernelSumRange_succ (U : ℕ) :
    kernelSumRange (fun x => x + 1) (U + 1) = (U + 2).choose 2 := by
  simpa only [Nat.add_assoc] using kernelSumRange_succ_all (U + 1)

theorem kernelSumRange_choose_two_all : ∀ n : ℕ,
    kernelSumRange (fun x => (x + 1).choose 2) n = (n + 1).choose 3
  | 0 => by decide
  | n + 1 => by
      rw [LocatorLowQuotient.kernelSumRange_succ, kernelSumRange_choose_two_all]
      simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
        (Nat.choose_succ_succ (n + 1) 2).symm

theorem kernelSumRange_choose_two (U : ℕ) :
    kernelSumRange (fun x => (x + 1).choose 2) (U + 1) =
      (U + 2).choose 3 := by
  simpa only [Nat.add_assoc] using kernelSumRange_choose_two_all (U + 1)

theorem kernelSumRange_uncapped (B U : ℕ) :
    kernelSumRange (fun x =>
      (x + 1) * (B + x) - (x + 1) * x / 2) (U + 1) =
      B * (U + 2).choose 2 + (U + 2).choose 3 := by
  rw [kernelSumRange_eq]
  simp_rw [term_eq]
  rw [Finset.sum_add_distrib]
  rw [← Finset.sum_mul]
  rw [← kernelSumRange_eq, kernelSumRange_succ]
  rw [← kernelSumRange_eq, kernelSumRange_choose_two]
  simp only [Nat.mul_comm]

def cappedTerm (B S x : ℕ) : ℕ :=
  let M := min S x
  (M + 1) * (B + x) - (M + 1) * M / 2

theorem min_sub_min_eq (T YS x : ℕ) (hx : x ≤ min T YS) :
    min (T - (min T YS - x)) (YS - (min T YS - x)) = x := by
  rcases le_total T YS with h | h
  · simp only [Nat.min_eq_left h] at hx ⊢
    omega
  · simp only [Nat.min_eq_right h] at hx ⊢
    omega

theorem channelCount_eq_cappedKernel (T YS S : ℕ) :
    channelCount T YS S =
      kernelSumRange
        (cappedTerm (T + 1 - min T YS) S) (min T YS + 1) := by
  unfold channelCount
  rw [kernelSumRange_eq, ← Finset.sum_range_reflect]
  rw [kernelSumRange_eq]
  refine Finset.sum_congr rfl ?_
  intro x hx
  have hx' : x ≤ min T YS := by
    have := Finset.mem_range.mp hx
    omega
  have hU : min T YS ≤ T := Nat.min_le_left _ _
  simp only [Nat.add_sub_cancel, cappedTerm]
  rw [min_sub_min_eq T YS x hx']
  have harg : T + 1 - (min T YS - x) =
      (T + 1 - min T YS) + x := by omega
  rw [harg]

def fastChannelCount (T YS S : ℕ) : ℕ :=
  let U := min T YS
  let B := T + 1 - U
  let k := min S U
  let n := U - k
  let C := (S + 1) * (B + S + 1) - (S + 1) * S / 2
  B * (k + 2).choose 2 + (k + 2).choose 3 +
    n * C + (S + 1) * (n * (n - 1) / 2)

theorem tail_term_eq (B S t : ℕ) :
    cappedTerm B S (S + 1 + t) =
      ((S + 1) * (B + S + 1) - (S + 1) * S / 2) +
        (S + 1) * t := by
  unfold cappedTerm
  rw [Nat.min_eq_left (by omega)]
  change (S + 1) * (B + (S + 1 + t)) - (S + 1) * S / 2 =
    ((S + 1) * (B + S + 1) - (S + 1) * S / 2) + (S + 1) * t
  rw [show B + (S + 1 + t) = (B + S + 1) + t by omega,
    Nat.mul_add]
  have hS : S ≤ B + S + 1 := by omega
  have hq : (S + 1) * S / 2 ≤ (S + 1) * (B + S + 1) :=
    (Nat.div_le_self ((S + 1) * S) 2).trans
      (Nat.mul_le_mul_left (S + 1) hS)
  exact Nat.sub_add_comm
    (n := (S + 1) * (B + S + 1)) (m := (S + 1) * t)
    (k := (S + 1) * S / 2) hq

theorem kernelSumRange_capped_prefix (B S k : ℕ) (hk : k ≤ S) :
    kernelSumRange (cappedTerm B S) (k + 1) =
      B * (k + 2).choose 2 + (k + 2).choose 3 := by
  calc
    kernelSumRange (cappedTerm B S) (k + 1) =
        kernelSumRange (fun x =>
          (x + 1) * (B + x) - (x + 1) * x / 2) (k + 1) := by
      rw [kernelSumRange_eq, kernelSumRange_eq]
      refine Finset.sum_congr rfl ?_
      intro x hx
      have hxk : x ≤ k := by
        have := Finset.mem_range.mp hx
        omega
      simp only [cappedTerm, Nat.min_eq_right (hxk.trans hk)]
    _ = B * (k + 2).choose 2 + (k + 2).choose 3 :=
      kernelSumRange_uncapped B k

theorem sum_Ico_capped_tail (B S U : ℕ) (hSU : S < U) :
    (∑ x ∈ Finset.Ico (S + 1) (U + 1), cappedTerm B S x) =
      (U - S) *
          ((S + 1) * (B + S + 1) - (S + 1) * S / 2) +
        (S + 1) * ((U - S) * (U - S - 1) / 2) := by
  rw [Finset.sum_Ico_eq_sum_range]
  have hsub : U + 1 - (S + 1) = U - S := by omega
  rw [hsub]
  simp_rw [tail_term_eq]
  rw [Finset.sum_add_distrib]
  rw [← Finset.mul_sum]
  simp only [Finset.sum_const, Finset.card_range, Nat.nsmul_eq_mul,
    Finset.sum_range_id]

theorem kernelSumRange_capped_closed (B S U : ℕ) :
    kernelSumRange (cappedTerm B S) (U + 1) =
      let k := min S U
      let n := U - k
      B * (k + 2).choose 2 + (k + 2).choose 3 +
        n * ((S + 1) * (B + S + 1) - (S + 1) * S / 2) +
          (S + 1) * (n * (n - 1) / 2) := by
  by_cases hSU : S < U
  · simp only [Nat.min_eq_left hSU.le]
    rw [kernelSumRange_eq]
    rw [← Finset.sum_range_add_sum_Ico (cappedTerm B S)
      (show S + 1 ≤ U + 1 by omega)]
    rw [← kernelSumRange_eq, kernelSumRange_capped_prefix B S S le_rfl,
      sum_Ico_capped_tail B S U hSU]
    simp only [Nat.add_assoc]
  · have hUS : U ≤ S := Nat.le_of_not_gt hSU
    simp only [Nat.min_eq_right hUS, Nat.sub_self, zero_mul,
      Nat.zero_sub, Nat.add_zero]
    exact kernelSumRange_capped_prefix B S U hUS

theorem channelCount_eq_fast (T YS S : ℕ) :
    channelCount T YS S = fastChannelCount T YS S := by
  rw [channelCount_eq_cappedKernel]
  rw [kernelSumRange_capped_closed]
  rfl

theorem choose_three_right (n : ℕ) :
    n.choose 3 = n * (n - 1) * (n - 2) / 6 := by
  rw [Nat.choose_eq_descFactorial_div_factorial]
  simp [Nat.descFactorial, Nat.factorial]
  congr 1
  ring

def evalChooseTwo (n : ℕ) : ℕ := n * (n - 1) / 2
def evalChooseThree (n : ℕ) : ℕ := n * (n - 1) * (n - 2) / 6

def evalChannelCount (T YS S : ℕ) : ℕ :=
  let U := min T YS
  let B := T + 1 - U
  let k := min S U
  let n := U - k
  let C := (S + 1) * (B + S + 1) - (S + 1) * S / 2
  B * evalChooseTwo (k + 2) + evalChooseThree (k + 2) +
    n * C + (S + 1) * (n * (n - 1) / 2)

theorem fastChannelCount_eq_eval (T YS S : ℕ) :
    fastChannelCount T YS S = evalChannelCount T YS S := by
  simp only [fastChannelCount, evalChannelCount, evalChooseTwo,
    evalChooseThree, Nat.choose_two_right, choose_three_right]

theorem channelCount_eq_eval (T YS S : ℕ) :
    channelCount T YS S = evalChannelCount T YS S :=
  (channelCount_eq_fast T YS S).trans (fastChannelCount_eq_eval T YS S)

open LocatorArbitraryPowerAvoidance Lower80899.Oracle
open LocatorPhase6800Oracle (rawFlag)
open RCN095 LocatorFactorAggregate

def evalPowerBandBudget
    (delta dT dY dS T YS S : ℕ) : ℕ → ℕ
  | 0 => 0
  | fuel + 1 =>
      delta * evalChannelCount T YS S +
        evalPowerBandBudget delta dT dY dS
          (T - dT) (YS - dY) (S - dS) fuel

theorem evalPowerBandBudget_eq
    (delta dT dY dS T YS S fuel : ℕ) :
    evalPowerBandBudget delta dT dY dS T YS S fuel =
      powerBandBudget delta dT dY dS T YS S fuel := by
  induction fuel generalizing T YS S with
  | zero => rfl
  | succ fuel ih =>
      simp only [evalPowerBandBudget, powerBandBudget]
      rw [← channelCount_eq_eval, ih]

def evalBand (s : SourceNumbers) (p : FlagDegree) : ℕ :=
  evalPowerBandBudget 50175 (total p) (middle p) p.all
    (s.totalCap - total p) (s.middleCap - middle p)
    (s.slopeCap - p.all) (s.fuel p)

theorem evalBand_eq (s : SourceNumbers) (p : FlagDegree) :
    evalBand s p = s.band p := by
  unfold evalBand SourceNumbers.band
  exact evalPowerBandBudget_eq _ _ _ _ _ _ _ _

def evalPowerBandBudgetThin
    (w Dh delta dc dT dY dS T YS S : ℕ) : ℕ → ℕ
  | 0 => 0
  | fuel + 1 =>
      delta * evalChannelCount T (min YS (thinTop w Dh S)) S +
        evalPowerBandBudgetThin w (Dh - delta - dc) delta dc dT dY dS
          (T - dT) (YS - dY) (S - dS) fuel

theorem evalPowerBandBudgetThin_eq
    (w Dh delta dc dT dY dS T YS S fuel : ℕ) :
    evalPowerBandBudgetThin w Dh delta dc dT dY dS T YS S fuel =
      powerBandBudgetThin w Dh delta dc dT dY dS T YS S fuel := by
  induction fuel generalizing Dh T YS S with
  | zero => rfl
  | succ fuel ih =>
      simp only [evalPowerBandBudgetThin, powerBandBudgetThin]
      rw [← channelCount_eq_eval, ih]

def evalBandThin (s : SourceNumbers) (p : FlagDegree) : ℕ :=
  evalPowerBandBudgetThin 131071 (s.contactCap p) 50175 (contactDec p)
    (total p) (middle p) p.all
    (s.totalCap - total p) (s.middleCap - middle p)
    (s.slopeCap - p.all) (s.fuel p)

theorem evalBandThin_eq (s : SourceNumbers) (p : FlagDegree) :
    evalBandThin s p = s.bandThin p := by
  unfold evalBandThin SourceNumbers.bandThin
  exact evalPowerBandBudgetThin_eq _ _ _ _ _ _ _ _ _ _ _

def FastRouteable (s : SourceNumbers) (p : FlagDegree) : Prop :=
  1 ≤ p.all ∧ total p ≤ s.totalCap ∧ middle p ≤ s.middleCap ∧
    p.all ≤ s.slopeCap ∧ (evalBandThin s p < s.gap ∨ evalBand s p < s.gap)

instance (s : SourceNumbers) (p : FlagDegree) :
    Decidable (FastRouteable s p) := by
  unfold FastRouteable
  infer_instance

theorem fastRouteable_iff (s : SourceNumbers) (p : FlagDegree) :
    FastRouteable s p ↔ s.Routeable p := by
  unfold FastRouteable SourceNumbers.Routeable
  rw [evalBand_eq, evalBandThin_eq, or_comm]

def FastSourceThresholdSufficient
    (s : SourceNumbers) (r v threshold : ℕ) : Prop :=
  11192 - (r + v) < threshold ∨ FastRouteable s (rawFlag r v threshold)

instance (s : SourceNumbers) (r v threshold : ℕ) :
    Decidable (FastSourceThresholdSufficient s r v threshold) := by
  unfold FastSourceThresholdSufficient
  infer_instance

theorem sufficient_route (s : SourceNumbers) (r v threshold z : ℕ)
    (hs : 11192 ≤ s.totalCap) (hz : r+v+z ≤ 11192) (ht : threshold ≤ z)
    (hc : FastSourceThresholdSufficient s r v threshold) :
    s.Routeable (rawFlag r v z) := by
  rcases hc with hbad | hroute
  · omega
  · exact Lower80899.PhaseRows.routeable_raw_mono_z s ht (hz.trans hs)
      ((fastRouteable_iff _ _).mp hroute)
end ProximityPrize.SubmissionLower.Lower80899.ThresholdFast
end MergedPart0
section MergedPart1
set_option Elab.async true
namespace ProximityPrize.SubmissionLower.Lower80899.ThresholdIndexed
open RCN095 LocatorFactorAggregate LocatorArbitraryPowerAvoidance
open LocatorPhase6800Oracle (rawFlag)
open Lower80899.Oracle Lower80899.ThresholdFast
open Lower80899.PhaseRows
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

def indexedThin (w Dh delta dc dT dY dS T YS S : ℕ) : ℕ → ℕ
  | 0 => 0
  | n+1 => indexedThin w Dh delta dc dT dY dS T YS S n +
      delta * evalChannelCount (T-n*dT)
        (min (YS-n*dY) (thinTop w (Dh-n*(delta+dc)) (S-n*dS))) (S-n*dS)

theorem indexedThin_shift (w Dh delta dc dT dY dS T YS S n : ℕ) :
    indexedThin w Dh delta dc dT dY dS T YS S (n+1) =
      delta * evalChannelCount T (min YS (thinTop w Dh S)) S +
        indexedThin w (Dh-delta-dc) delta dc dT dY dS (T-dT) (YS-dY) (S-dS) n := by
  induction n with
  | zero => simp [indexedThin]
  | succ n ih =>
      rw [indexedThin, ih, indexedThin]
      have shift (x d : ℕ) : x-(n+1)*d = (x-d)-n*d := by
        rw [Nat.add_mul, Nat.one_mul, Nat.sub_sub]
        omega
      rw [shift T dT, shift YS dY, shift S dS, shift Dh (delta+dc)]
      rw [Nat.sub_sub]
      omega

theorem indexedThin_eq (w Dh delta dc dT dY dS T YS S fuel : ℕ) :
    indexedThin w Dh delta dc dT dY dS T YS S fuel =
      evalPowerBandBudgetThin w Dh delta dc dT dY dS T YS S fuel := by
  induction fuel generalizing Dh T YS S with
  | zero => rfl
  | succ fuel ih =>
      rw [indexedThin_shift, evalPowerBandBudgetThin, ih]

def indexedBand (s : SourceNumbers) (p : FlagDegree) : ℕ :=
  indexedThin 131071 (s.contactCap p) 50175 (contactDec p)
    (total p) (middle p) p.all (s.totalCap-total p)
    (s.middleCap-middle p) (s.slopeCap-p.all) (s.fuel p)

theorem indexedBand_eq (s : SourceNumbers) (p : FlagDegree) :
    indexedBand s p = evalBandThin s p := indexedThin_eq _ _ _ _ _ _ _ _ _ _ _

def IndexedSufficient (s : SourceNumbers) (r v threshold : ℕ) : Prop :=
  11192-(r+v) < threshold ∨
    let p := rawFlag r v threshold
    1 ≤ p.all ∧ total p ≤ s.totalCap ∧ middle p ≤ s.middleCap ∧
      p.all ≤ s.slopeCap ∧ indexedBand s p < s.gap
instance (s : SourceNumbers) (r v threshold : ℕ) :
    Decidable (IndexedSufficient s r v threshold) := by
  unfold IndexedSufficient; infer_instance

theorem sufficient_of_indexed (s : SourceNumbers) (r v threshold : ℕ)
    (h : IndexedSufficient s r v threshold) :
    FastSourceThresholdSufficient s r v threshold := by
  rcases h with h | ⟨hr,ht,hy,hs,hb⟩
  · exact Or.inl h
  · exact Or.inr ⟨hr,ht,hy,hs,Or.inl ((indexedBand_eq _ _) ▸ hb)⟩

end ProximityPrize.SubmissionLower.Lower80899.ThresholdIndexed

namespace ProximityPrize.SubmissionLower.Lower80899.BandPolynomial
open scoped BigOperators
open LocatorLowQuotient Lower80899.ThresholdFast
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

def boxPoly (w A B C : ℤ) : ℤ :=
  (C+w)*(3*(A+w)*(C+2*w)+C*(C+2*w)+6*A*B+9*w*B+3*B*C+3*B*B)

theorem choose_two_scaled (c : ℕ) :
    2 * (c+2).choose 2 = (c+2)*(c+1) := by
  have h := Nat.descFactorial_eq_factorial_mul_choose (c+2) 2
  simpa [Nat.descFactorial, Nat.factorial, Nat.mul_comm] using h.symm

theorem choose_three_scaled (c : ℕ) :
    6 * (c+2).choose 3 = (c+2)*(c+1)*c := by
  have h := Nat.descFactorial_eq_factorial_mul_choose (c+2) 3
  simpa [Nat.descFactorial, Nat.factorial, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using h.symm

theorem half_succ (c : ℕ) : 2*((c+1)*c/2) = (c+1)*c := by
  have h : 2 ∣ (c+1)*c := by
    simpa [Nat.mul_comm, Nat.add_comm] using
      (even_iff_two_dvd.mp (Nat.even_mul_succ_self c))
  simpa [Nat.mul_comm] using Nat.div_mul_cancel h

theorem half_pred (b : ℕ) : 2*(b*(b-1)/2)+b = b*b := by
  cases b with
  | zero => decide
  | succ b =>
      simp only [Nat.add_sub_cancel]
      rw [half_succ]
      ring

theorem channel_raw (a b c : ℕ) :
    6 * (channelCount (a+b+c) (b+c) c : ℤ) = boxPoly 1 a b c := by
  rw [channelCount_eq_fast]
  have hm : min (a+b+c) (b+c) = b+c := min_eq_right (by omega)
  have hk : min c (b+c) = c := min_eq_left (by omega)
  simp only [fastChannelCount, hm, hk]
  have hA : a+b+c+1-(b+c) = a+1 := by omega
  have hB : b+c-c = b := by omega
  rw [hA, hB]
  have hsub : (c+1)*c/2 ≤ (c+1)*(a+1+c+1) :=
    (Nat.div_le_self _ _).trans (Nat.mul_le_mul_left _ (by omega))
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_sub hsub]
  have h2 : (2 : ℤ)*((c+2).choose 2 : ℤ) = (c+2)*(c+1) := by
    exact_mod_cast choose_two_scaled c
  have h3 : (6 : ℤ)*((c+2).choose 3 : ℤ) = (c+2)*(c+1)*c := by
    exact_mod_cast choose_three_scaled c
  have hc : (2 : ℤ)*(((c+1)*c/2 : ℕ) : ℤ) = (c+1)*c := by
    exact_mod_cast half_succ c
  have hb : (2 : ℤ)*((b*(b-1)/2 : ℕ) : ℤ)+b = b*b := by
    exact_mod_cast half_pred b
  unfold boxPoly
  nlinarith only [h3, congrArg (fun x : ℤ => 3*(a+1)*x) h2,
    congrArg (fun x : ℤ => 3*(b : ℤ)*x) hc,
    congrArg (fun x : ℤ => 3*(c+1)*x) hb]

theorem channel_normalized (T YS S : ℕ) :
    channelCount T YS S =
      channelCount (T-min T YS+(min T YS-min S (min T YS))+min S (min T YS))
        (min T YS-min S (min T YS)+min S (min T YS)) (min S (min T YS)) := by
  have hU := Nat.min_le_left T YS
  have hk := Nat.min_le_right S (min T YS)
  have hT : T-min T YS+(min T YS-min S (min T YS))+min S (min T YS) = T := by omega
  have hY : min T YS-min S (min T YS)+min S (min T YS) = min T YS := by omega
  rw [hT, hY]
  rw [channelCount_eq_cappedKernel, channelCount_eq_cappedKernel]
  rw [min_eq_right hU]
  rw [kernelSumRange_eq, kernelSumRange_eq]
  apply Finset.sum_congr rfl
  intro x hx
  have hx' : x ≤ min T YS := by have := Finset.mem_range.mp hx; omega
  unfold cappedTerm
  rw [min_assoc, min_eq_right hx']

theorem channel_poly (T YS S : ℕ) :
    6*(channelCount T YS S : ℤ) =
      boxPoly 1 ((T-min T YS : ℕ) : ℤ) ((min T YS-min S (min T YS) : ℕ) : ℤ) (min S (min T YS) : ℕ) := by
  rw [channel_normalized T YS S]
  exact channel_raw _ _ _

theorem boxPoly_scaled (w a b c : ℤ) :
    boxPoly w (w*a) (w*b) (w*c) = w^3*boxPoly 1 a b c := by
  unfold boxPoly
  ring

theorem boxPoly_mono (w a b c A B C : ℤ)
    (hw : 0 ≤ w) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hA : a ≤ A) (hB : b ≤ B) (hC : c ≤ C) :
    boxPoly w a b c ≤ boxPoly w A B C := by
  have hA0 := ha.trans hA
  have hB0 := hb.trans hB
  have hC0 := hc.trans hC
  unfold boxPoly
  gcongr <;> positivity

theorem channel_thin_bound (T YS S Dh : ℕ) :
    6*131071^3*(channelCount T (min YS ((Dh+S-1)/131071)) S : ℤ) ≤
      boxPoly 131071
        (131071*T-min (131071*T) (min (131071*YS) (Dh+S))+131071)
        (min (131071*T) (min (131071*YS) (Dh+S))-
          min (131071*S) (min (131071*T) (min (131071*YS) (Dh+S))))
        (min (131071*S) (min (131071*T) (min (131071*YS) (Dh+S)))) := by
  let U := min T (min YS ((Dh+S-1)/131071))
  let C := min S U
  let V : ℤ := min (131071*T) (min (131071*YS) (Dh+S))
  let K : ℤ := min (131071*S) V
  have hU : U ≤ T := Nat.min_le_left _ _
  have hC : C ≤ U := Nat.min_le_right _ _
  have hround : 131071*(U : ℤ) ≤ V ∧ V ≤ 131071*(U : ℤ)+131071 := by
    dsimp [U, V]
    omega
  have hK : 131071*(C : ℤ) ≤ K := by dsimp [C, K]; omega
  have hB : 131071*((U-C : ℕ) : ℤ) ≤ V-K := by
    dsimp [C, K]
    omega
  have hA : 131071*((T-U : ℕ) : ℤ) ≤ 131071*T-V+131071 := by omega
  have hm := boxPoly_mono 131071
    (131071*((T-U : ℕ) : ℤ)) (131071*((U-C : ℕ) : ℤ)) (131071*C)
    (131071*T-V+131071) (V-K) K (by norm_num) (by positivity)
    (by positivity) (by positivity) hA hB hK
  rw [boxPoly_scaled, ← channel_poly] at hm
  convert hm using 1 <;> push_cast <;> ring

structure Affine where
  constant : ℤ
  slope : ℤ
  deriving DecidableEq, Repr

def Affine.eval (a : Affine) (i : ℕ) : ℤ := a.constant+a.slope*i

def triplePrefix (a b c : Affine) (n : ℕ) : ℤ :=
  let x : ℤ := n
  12*x*(a.constant*b.constant*c.constant)+
  6*x*(x-1)*(a.slope*b.constant*c.constant+a.constant*b.slope*c.constant+a.constant*b.constant*c.slope)+
  2*x*(x-1)*(2*x-1)*(a.slope*b.slope*c.constant+a.slope*b.constant*c.slope+a.constant*b.slope*c.slope)+
  3*x*x*(x-1)*(x-1)*(a.slope*b.slope*c.slope)

theorem triplePrefix_eq (a b c : Affine) (n : ℕ) :
    triplePrefix a b c n = 12*∑ i ∈ Finset.range n, a.eval i*b.eval i*c.eval i := by
  induction n with
  | zero => simp [triplePrefix]
  | succ n ih =>
      rw [Finset.sum_range_succ, mul_add, ← ih]
      simp only [triplePrefix, Affine.eval, Nat.cast_add, Nat.cast_one]
      ring

def Affine.add (a b : Affine) : Affine := ⟨a.constant+b.constant,a.slope+b.slope⟩
def Affine.sub (a b : Affine) : Affine := ⟨a.constant-b.constant,a.slope-b.slope⟩
def Affine.scale (a : Affine) (k : ℤ) : Affine := ⟨k*a.constant,k*a.slope⟩
def Affine.plus (a : Affine) (k : ℤ) : Affine := ⟨a.constant+k,a.slope⟩

@[simp] theorem Affine.eval_add (a b : Affine) (i : ℕ) :
    (a.add b).eval i = a.eval i+b.eval i := by simp [Affine.add, Affine.eval]; ring
@[simp] theorem Affine.eval_sub (a b : Affine) (i : ℕ) :
    (a.sub b).eval i = a.eval i-b.eval i := by simp [Affine.sub, Affine.eval]; ring
@[simp] theorem Affine.eval_scale (a : Affine) (k : ℤ) (i : ℕ) :
    (a.scale k).eval i = k*a.eval i := by simp [Affine.scale, Affine.eval]; ring
@[simp] theorem Affine.eval_plus (a : Affine) (k : ℤ) (i : ℕ) :
    (a.plus k).eval i = a.eval i+k := by simp [Affine.plus, Affine.eval]; ring

def boxPrefix (a b c : Affine) (n : ℕ) : ℤ :=
  3*triplePrefix (c.plus 131071) (a.plus 131071) (c.plus (2*131071)) n+
  triplePrefix (c.plus 131071) c (c.plus (2*131071)) n+
  6*triplePrefix (c.plus 131071) a b n+
  9*131071*triplePrefix (c.plus 131071) b ⟨1,0⟩ n+
  3*triplePrefix (c.plus 131071) b c n+
  3*triplePrefix (c.plus 131071) b b n

def factoredBoxPrefix (a b c : Affine) (n : ℕ) : ℤ :=
  if n = 0 then 0 else
  let x : ℤ := n
  let w : ℤ := 131071
  let A := a.constant
  let B := b.constant
  let C := c.constant
  let α := a.slope
  let β := b.slope
  let γ := c.slope
  let q0 := 3*(A+w)*(C+2*w)+C*(C+2*w)+6*A*B+9*w*B+3*B*C+3*B*B
  let q1 := 3*((A+w)*γ+α*(C+2*w))+γ*(2*C+2*w)+
    6*(A*β+α*B)+9*w*β+3*(B*γ+β*C)+6*B*β
  let q2 := 3*α*γ+γ*γ+6*α*β+3*β*γ+3*β*β
  let s0 := 12*x
  let s1 := 6*x*(x-1)
  let s2 := 2*x*(x-1)*(2*x-1)
  let s3 := 3*x*x*(x-1)*(x-1)
  q0*(s0*(C+w)+s1*γ)+q1*(s1*(C+w)+s2*γ)+q2*(s2*(C+w)+s3*γ)

theorem factoredBoxPrefix_eq (a b c : Affine) (n : ℕ) :
    factoredBoxPrefix a b c n = boxPrefix a b c n := by
  unfold factoredBoxPrefix
  split_ifs with hn
  · subst n
    simp [boxPrefix, triplePrefix]
  · simp only [boxPrefix, triplePrefix, Affine.plus]
    ring

theorem boxPrefix_eq (a b c : Affine) (n : ℕ) :
    boxPrefix a b c n =
      12*∑ i ∈ Finset.range n, boxPoly 131071 (a.eval i) (b.eval i) (c.eval i) := by
  simp only [boxPrefix, triplePrefix_eq, Affine.eval_plus]
  apply Eq.symm
  calc
    _ = ∑ i ∈ Finset.range n, 12*boxPoly 131071 (a.eval i) (b.eval i) (c.eval i) := by rw [Finset.mul_sum]
    _ = ∑ i ∈ Finset.range n,
        ((3*(12*((c.eval i+131071)*(a.eval i+131071)*(c.eval i+2*131071))))+
        (12*((c.eval i+131071)*c.eval i*(c.eval i+2*131071)))+
        (6*(12*((c.eval i+131071)*a.eval i*b.eval i)))+
        (9*131071*(12*((c.eval i+131071)*b.eval i*(Affine.eval ⟨1,0⟩ i))))+
        (3*(12*((c.eval i+131071)*b.eval i*c.eval i)))+
        (3*(12*((c.eval i+131071)*b.eval i*b.eval i)))) := by
      apply Finset.sum_congr rfl
      intro i _
      simp only [boxPoly, Affine.eval]
      ring
    _ = _ := by simp only [Finset.sum_add_distrib, ← Finset.mul_sum]

theorem boxPrefix_interval (a b c : Affine) (lo hi : ℕ) (h : lo ≤ hi) :
    boxPrefix a b c hi-boxPrefix a b c lo =
      12*∑ i ∈ Finset.Ico lo hi, boxPoly 131071 (a.eval i) (b.eval i) (c.eval i) := by
  rw [boxPrefix_eq, boxPrefix_eq]
  rw [← Finset.sum_range_add_sum_Ico _ h]
  ring

theorem Affine.nonneg_between (a : Affine) (lo hi i : ℕ)
    (hlo : lo ≤ i) (hhi : i ≤ hi) (h0 : 0 ≤ a.eval lo) (h1 : 0 ≤ a.eval hi) :
    0 ≤ a.eval i := by
  unfold Affine.eval at *
  rcases le_total 0 a.slope with hs | hs
  · have hh := mul_le_mul_of_nonneg_left (show (lo : ℤ) ≤ i by omega) hs
    omega
  · have hh := mul_le_mul_of_nonpos_left (show (i : ℤ) ≤ hi by omega) hs
    omega

end ProximityPrize.SubmissionLower.Lower80899.BandPolynomial

namespace ProximityPrize.SubmissionLower.Lower80899.CompressedBand
open scoped BigOperators
open Lower80899.BandPolynomial Lower80899.ThresholdIndexed
open Lower80899.ThresholdFast LocatorLowQuotient
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

structure Input where
  T : ℕ
  YS : ℕ
  S : ℕ
  Dh : ℕ
  dT : ℕ
  dY : ℕ
  dS : ℕ
  dDh : ℕ
  fuel : ℕ
  deriving DecidableEq, Repr

def Input.atT (p : Input) : Affine := ⟨p.T,-(p.dT : ℤ)⟩
def Input.atY (p : Input) : Affine := ⟨p.YS,-(p.dY : ℤ)⟩
def Input.atS (p : Input) : Affine := ⟨p.S,-(p.dS : ℤ)⟩
def Input.atDh (p : Input) : Affine := ⟨p.Dh,-(p.dDh : ℤ)⟩
def Input.count (p : Input) (i : ℕ) : ℕ :=
  channelCount (p.T-i*p.dT)
    (min (p.YS-i*p.dY) ((p.Dh-i*p.dDh+(p.S-i*p.dS)-1)/131071)) (p.S-i*p.dS)

def Input.dh (p : Input) (code : ℕ) : Affine := if 6 ≤ code then p.atDh else ⟨0,0⟩
def Input.u (p : Input) (code : ℕ) : Affine :=
  if code/2%3 = 0 then p.atT.scale 131071
  else if code/2%3 = 1 then p.atY.scale 131071
  else (p.dh code).add p.atS
def Input.c (p : Input) (code : ℕ) : Affine :=
  if code%2 = 0 then p.atS.scale 131071 else p.u code
def Input.a (p : Input) (code : ℕ) : Affine := ((p.atT.scale 131071).sub (p.u code)).plus 131071
def Input.b (p : Input) (code : ℕ) : Affine := (p.u code).sub (p.c code)

def conditions (p : Input) (code : ℕ) : List Affine :=
  [p.atT,p.atY,p.atS,if 6 ≤ code then p.atDh else p.atDh.scale (-1),
    (p.atT.scale 131071).sub (p.u code),
    (p.atY.scale 131071).sub (p.u code),
    ((p.dh code).add p.atS).sub (p.u code),
    (p.atS.scale 131071).sub (p.c code),
    (p.u code).sub (p.c code)]

def ValidAt (p : Input) (code i : ℕ) : Prop :=
  ∀ a ∈ conditions p code, 0 ≤ a.eval i
def FastValidAt (p : Input) (code i : ℕ) : Prop :=
  let t := p.atT.eval i
  let y := p.atY.eval i
  let s := p.atS.eval i
  let u := (p.u code).eval i
  let c := (p.c code).eval i
  0 ≤ t ∧ 0 ≤ y ∧ 0 ≤ s ∧
    0 ≤ (if 6 ≤ code then p.atDh else p.atDh.scale (-1)).eval i ∧
    u ≤ 131071*t ∧ u ≤ 131071*y ∧ u ≤ (p.dh code).eval i+s ∧
    c ≤ 131071*s ∧ c ≤ u
instance (p : Input) (code i : ℕ) : Decidable (FastValidAt p code i) := by
  unfold FastValidAt
  infer_instance

theorem validAt_iff_fast (p : Input) (code i : ℕ) :
    ValidAt p code i ↔ FastValidAt p code i := by
  simp only [ValidAt, FastValidAt, conditions, List.mem_cons,
    List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
    Affine.eval_sub, Affine.eval_scale, Affine.eval_add, sub_nonneg]

instance (p : Input) (code i : ℕ) : Decidable (ValidAt p code i) :=
  decidable_of_iff (FastValidAt p code i) (validAt_iff_fast p code i).symm

theorem validAt_between (p : Input) (code lo hi i : ℕ)
    (hlo : lo ≤ i) (hhi : i ≤ hi) (h0 : ValidAt p code lo) (h1 : ValidAt p code hi) :
    ValidAt p code i := by
  intro a ha
  exact a.nonneg_between lo hi i hlo hhi (h0 a ha) (h1 a ha)

theorem linear_cast (t d i : ℕ) (h : 0 ≤ Affine.eval ⟨t,-(d : ℤ)⟩ i) :
    ((t-i*d : ℕ) : ℤ) = Affine.eval ⟨t,-(d : ℤ)⟩ i := by
  simp only [Affine.eval, neg_mul] at *
  have hc : ((i*d : ℕ) : ℤ) = (d : ℤ)*i := by push_cast; ring
  omega

theorem validAt_bound (p : Input) (code i : ℕ) (h : ValidAt p code i) :
    6*131071^3*(p.count i : ℤ) ≤
      boxPoly 131071 ((p.a code).eval i) ((p.b code).eval i) ((p.c code).eval i) := by
  simp only [ValidAt, conditions, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq] at h
  rcases h with ⟨hT,hY,hS,hD,hU0,hU1,hU2,hC0,hC1⟩
  have htc := linear_cast p.T p.dT i hT
  have hyc := linear_cast p.YS p.dY i hY
  have hsc := linear_cast p.S p.dS i hS
  change ((p.T-i*p.dT : ℕ) : ℤ) = p.atT.eval i at htc
  change ((p.YS-i*p.dY : ℕ) : ℤ) = p.atY.eval i at hyc
  change ((p.S-i*p.dS : ℕ) : ℤ) = p.atS.eval i at hsc
  have hdc : ((p.Dh-i*p.dDh : ℕ) : ℤ) = (p.dh code).eval i := by
    unfold Input.dh
    split_ifs with hd
    · simp only [hd, ↓reduceIte] at hD
      exact linear_cast p.Dh p.dDh i hD
    · simp only [hd, ↓reduceIte, Affine.eval_scale] at hD
      simp only [Input.atDh, Affine.eval, neg_mul] at hD ⊢
      have hc : ((i*p.dDh : ℕ) : ℤ) = (p.dDh : ℤ)*i := by push_cast; ring
      omega
  simp only [Affine.eval_sub, Affine.eval_scale, Affine.eval_add] at hU0 hU1 hU2 hC0 hC1
  have hue : (p.u code).eval i =
      min (131071*p.atT.eval i) (min (131071*p.atY.eval i) ((p.dh code).eval i+p.atS.eval i)) := by
    by_cases h0 : code/2%3 = 0
    · simp only [Input.u, h0, ↓reduceIte, Affine.eval_scale] at hU0 hU1 hU2 ⊢
      omega
    · by_cases h1 : code/2%3 = 1
      · simp only [Input.u, h0, h1, Nat.one_ne_zero, ↓reduceIte, Affine.eval_scale] at hU0 hU1 hU2 ⊢
        omega
      · simp only [Input.u, h0, h1, Nat.one_ne_zero, ↓reduceIte, Affine.eval_add] at hU0 hU1 hU2 ⊢
        omega
  have hce : (p.c code).eval i = min (131071*p.atS.eval i) ((p.u code).eval i) := by
    by_cases h0 : code%2 = 0 <;>
      simp only [Input.c, h0, ↓reduceIte, Affine.eval_scale] at hC0 hC1 ⊢ <;> omega
  have hb := channel_thin_bound (p.T-i*p.dT) (p.YS-i*p.dY) (p.S-i*p.dS) (p.Dh-i*p.dDh)
  push_cast at hb
  rw [htc,hyc,hsc,hdc,← hue,← hce] at hb
  norm_num only [Int.reducePow, Int.reduceMul]
  simpa only [Input.count,Input.a,Input.b,Affine.eval_plus,Affine.eval_sub,Affine.eval_scale] using hb

def RunValid (p : Input) (start : ℕ) (run : Run) : Prop :=
  start < run.stop ∧ run.stop ≤ p.fuel ∧
    ValidAt p run.code start ∧ ValidAt p run.code (run.stop-1)
instance (p : Input) (start : ℕ) (run : Run) : Decidable (RunValid p start run) := by
  unfold RunValid; infer_instance

def runUpper (p : Input) (start : ℕ) (run : Run) : ℤ :=
  factoredBoxPrefix (p.a run.code) (p.b run.code) (p.c run.code) run.stop-
  factoredBoxPrefix (p.a run.code) (p.b run.code) (p.c run.code) start

theorem runValid_bound (p : Input) (start : ℕ) (run : Run)
    (h : RunValid p start run) :
    72*131071^3*(∑ i ∈ Finset.Ico start run.stop, (p.count i : ℤ)) ≤ runUpper p start run := by
  rw [runUpper, factoredBoxPrefix_eq, factoredBoxPrefix_eq, boxPrefix_interval _ _ _ _ _ h.1.le]
  have hs : (∑ i ∈ Finset.Ico start run.stop, 6*131071^3*(p.count i : ℤ)) ≤
      ∑ i ∈ Finset.Ico start run.stop,
        boxPoly 131071 ((p.a run.code).eval i) ((p.b run.code).eval i) ((p.c run.code).eval i) := by
    apply Finset.sum_le_sum
    intro i hi
    exact validAt_bound p run.code i (validAt_between p run.code start (run.stop-1) i
      (Finset.mem_Ico.mp hi).1 (by have := (Finset.mem_Ico.mp hi).2; omega) h.2.2.1 h.2.2.2)
  rw [← Finset.mul_sum] at hs
  linarith

def RunsValid (p : Input) : ℕ → List Run → Prop
  | start, [] => start = p.fuel
  | start, run::runs => RunValid p start run ∧ RunsValid p run.stop runs
instance (p : Input) (start : ℕ) (runs : List Run) : Decidable (RunsValid p start runs) := by
  induction runs generalizing start with
  | nil => unfold RunsValid; infer_instance
  | cons run runs ih => unfold RunsValid; infer_instance

def runsUpper (p : Input) : ℕ → List Run → ℤ
  | _, [] => 0
  | start, run::runs => runUpper p start run+runsUpper p run.stop runs

theorem runsValid_bound (p : Input) (start : ℕ) (runs : List Run)
    (h : RunsValid p start runs) :
    72*131071^3*(∑ i ∈ Finset.Ico start p.fuel, (p.count i : ℤ)) ≤ runsUpper p start runs := by
  induction runs generalizing start with
  | nil => simp only [RunsValid] at h; simp [h, runsUpper]
  | cons run runs ih =>
      have h0 := runValid_bound p start run h.1
      have h1 := ih run.stop h.2
      rw [← Finset.sum_Ico_consecutive _ h.1.1.le h.1.2.1]
      simp only [runsUpper]
      linarith

open Lower80899.Oracle LocatorArbitraryPowerAvoidance
open RCN095 LocatorFactorAggregate
open LocatorPhase6800Oracle (rawFlag)

def ofSource (s : SourceNumbers) (p : FlagDegree) : Input :=
  ⟨s.totalCap-total p,s.middleCap-middle p,s.slopeCap-p.all,s.contactCap p,
    total p,middle p,p.all,50175+contactDec p,s.fuel p⟩

theorem indexed_sum (p : Input) (dc n : ℕ) (hd : p.dDh = 50175+dc) :
    (indexedThin 131071 p.Dh 50175 dc p.dT p.dY p.dS p.T p.YS p.S n : ℤ) =
      50175*∑ i ∈ Finset.range n, (p.count i : ℤ) := by
  induction n with
  | zero => simp [indexedThin]
  | succ n ih =>
      rw [indexedThin, Nat.cast_add, Nat.cast_mul, ih, Finset.sum_range_succ]
      simp only [Input.count, channelCount_eq_eval, thinTop, hd]
      push_cast
      ring

theorem source_sum (s : SourceNumbers) (p : FlagDegree) :
    (indexedBand s p : ℤ) =
      50175*∑ i ∈ Finset.range (ofSource s p).fuel, ((ofSource s p).count i : ℤ) :=
  indexed_sum (ofSource s p) (contactDec p) (s.fuel p) rfl

def Sufficient (s : SourceNumbers) (r v threshold : ℕ) (runs : List Run) : Prop :=
  11192-(r+v) < threshold ∨
    let p := rawFlag r v threshold
    1 ≤ p.all ∧ total p ≤ s.totalCap ∧ middle p ≤ s.middleCap ∧ p.all ≤ s.slopeCap ∧
      RunsValid (ofSource s p) 0 runs ∧
      50175*runsUpper (ofSource s p) 0 runs < (s.gap : ℤ)*(72*131071^3)
instance (s : SourceNumbers) (r v threshold : ℕ) (runs : List Run) :
    Decidable (Sufficient s r v threshold runs) := by
  unfold Sufficient; infer_instance

theorem sufficient_sound (s : SourceNumbers) (r v threshold : ℕ) (runs : List Run)
    (h : Sufficient s r v threshold runs) : FastSourceThresholdSufficient s r v threshold := by
  rcases h with h | ⟨hr,ht,hy,hs,hvalid,hgap⟩
  · exact Or.inl h
  apply sufficient_of_indexed
  refine Or.inr ⟨hr,ht,hy,hs,?_⟩
  have hb := runsValid_bound (ofSource s (rawFlag r v threshold)) 0 runs hvalid
  rw [Nat.Ico_zero_eq_range] at hb
  have he := source_sum s (rawFlag r v threshold)
  have hi : (indexedBand s (rawFlag r v threshold) : ℤ) < s.gap := by
    nlinarith only [hgap, congrArg (fun x : ℤ => (72*131071^3)*x) he,
      mul_le_mul_of_nonneg_left hb (show (0 : ℤ) ≤ 50175 by norm_num)]
  exact_mod_cast hi

end ProximityPrize.SubmissionLower.Lower80899.CompressedBand
end MergedPart1
section MergedPart2
namespace ProximityPrize.SubmissionLower.FinalThreshold6815
open Lower80899.CompressedBand Lower80899.BandPolynomial Lower80899.Oracle Lower80899.ThresholdFast
open LocatorPhase6800Oracle (rawFlag)
open RCN095 LocatorFactorAggregate LocatorArbitraryPowerAvoidance LocatorLowQuotient
set_option autoImplicit false
set_option maxRecDepth 100000

def minK (a b : ℕ) : ℕ := cond (Nat.ble a b) a b

theorem minK_eq (a b : ℕ) : minK a b = min a b := by
  unfold minK
  by_cases h : a ≤ b
  · rw [Nat.ble_eq_true_of_le h, min_eq_left h]; rfl
  · rw [show Nat.ble a b = false from Bool.eq_false_iff.mpr (fun hb => h (Nat.le_of_ble_eq_true hb)),
      min_eq_right (by omega)]; rfl

def channelK (T YS S : ℕ) : ℕ :=
  let U := minK T YS
  let B := Nat.sub (Nat.add T 1) U
  let k := minK S U
  let n := Nat.sub U k
  let S1 := Nat.add S 1
  let C := Nat.sub (Nat.mul S1 (Nat.add (Nat.add B S) 1)) (Nat.div (Nat.mul S1 S) 2)
  let k2 := Nat.add k 2
  Nat.add (Nat.add (Nat.add (Nat.mul B (Nat.div (Nat.mul k2 (Nat.sub k2 1)) 2))
    (Nat.div (Nat.mul (Nat.mul k2 (Nat.sub k2 1)) (Nat.sub k2 2)) 6))
    (Nat.mul n C)) (Nat.mul S1 (Nat.div (Nat.mul n (Nat.sub n 1)) 2))

theorem channelK_eq (T YS S : ℕ) : channelK T YS S = evalChannelCount T YS S := by
  simp only [channelK, evalChannelCount, evalChooseTwo, evalChooseThree, minK_eq]
  rfl

def thinLoopK (w delta dc dT dY dS fuel : ℕ) : ℕ → ℕ → ℕ → ℕ → ℕ :=
  Nat.rec (motive := fun _ => ℕ → ℕ → ℕ → ℕ → ℕ) (fun _ _ _ _ => 0)
    (fun _ ih Dh T YS S => Nat.add
      (Nat.mul delta (channelK T (minK YS (Nat.div (Nat.sub (Nat.add Dh S) 1) w)) S))
      (ih (Nat.sub (Nat.sub Dh delta) dc) (Nat.sub T dT) (Nat.sub YS dY) (Nat.sub S dS))) fuel

theorem thinLoopK_eq (w delta dc dT dY dS fuel Dh T YS S : ℕ) :
    thinLoopK w delta dc dT dY dS fuel Dh T YS S =
      evalPowerBandBudgetThin w Dh delta dc dT dY dS T YS S fuel := by
  induction fuel generalizing Dh T YS S with
  | zero => rfl
  | succ fuel ih =>
    show Nat.add _ (thinLoopK w delta dc dT dY dS fuel _ _ _ _) = _
    rw [ih, evalPowerBandBudgetThin, channelK_eq, minK_eq]
    rfl

def bandThinK (s : SourceNumbers) (p : FlagDegree) : ℕ :=
  thinLoopK 131071 50175 (contactDec p) (total p) (middle p) p.all (s.fuel p)
    (s.contactCap p) (s.totalCap - total p) (s.middleCap - middle p) (s.slopeCap - p.all)

theorem bandThinK_eq (s : SourceNumbers) (p : FlagDegree) : bandThinK s p = evalBandThin s p :=
  thinLoopK_eq _ _ _ _ _ _ _ _ _ _ _

def fastK (s : SourceNumbers) (r v threshold : ℕ) : Bool :=
  Nat.blt (11192-(r+v)) threshold ||
    (let p := rawFlag r v threshold
     Nat.ble 1 p.all && Nat.ble (total p) s.totalCap && Nat.ble (middle p) s.middleCap &&
       Nat.ble p.all s.slopeCap && Nat.blt (bandThinK s p) s.gap)

theorem fastK_sound (s : SourceNumbers) (r v threshold : ℕ) (h : fastK s r v threshold = true) :
    FastSourceThresholdSufficient s r v threshold := by
  simp only [fastK, Bool.or_eq_true, Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq, bandThinK_eq] at h
  rcases h with h | ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩
  · exact Or.inl h
  · exact Or.inr ⟨h1, h2, h3, h4, Or.inl h5⟩

def validN (p : Input) (code i : ℕ) : Bool :=
  let t := p.T - i*p.dT
  let y := p.YS - i*p.dY
  let s := p.S - i*p.dS
  let hasD := Nat.ble 6 code
  let dh := cond hasD (p.Dh - i*p.dDh) 0
  let m := code/2%3
  let u := cond (Nat.beq m 0) (131071*t) (cond (Nat.beq m 1) (131071*y) (dh+s))
  let c := cond (Nat.beq (code%2) 0) (131071*s) u
  Nat.ble (i*p.dT) p.T && Nat.ble (i*p.dY) p.YS && Nat.ble (i*p.dS) p.S &&
    cond hasD (Nat.ble (i*p.dDh) p.Dh) (Nat.ble p.Dh (i*p.dDh)) &&
    Nat.ble u (131071*t) && Nat.ble u (131071*y) && Nat.ble u (dh+s) &&
    Nat.ble c (131071*s) && Nat.ble c u

theorem affine_cast (t d i : ℕ) (h : i*d ≤ t) :
    Affine.eval ⟨t,-(d : ℤ)⟩ i = ((t - i*d : ℕ) : ℤ) := by
  simp only [Affine.eval]
  push_cast [Nat.cast_sub h]
  ring

theorem validN_sound (p : Input) (code i : ℕ) (h : validN p code i = true) : ValidAt p code i := by
  rw [validAt_iff_fast]
  unfold validN at h
  simp only [Bool.and_eq_true, Nat.ble_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hT, hY⟩, hS⟩, hD⟩, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩ := h
  have et : p.atT.eval i = ((p.T - i*p.dT : ℕ) : ℤ) := affine_cast _ _ _ hT
  have ey : p.atY.eval i = ((p.YS - i*p.dY : ℕ) : ℤ) := affine_cast _ _ _ hY
  have es : p.atS.eval i = ((p.S - i*p.dS : ℕ) : ℤ) := affine_cast _ _ _ hS
  generalize p.T - i*p.dT = t at et h1 h2 h3 h4 h5
  generalize p.YS - i*p.dY = y at ey h1 h2 h3 h4 h5
  generalize p.S - i*p.dS = s at es h1 h2 h3 h4 h5
  have key : 0 ≤ (if 6 ≤ code then p.atDh else p.atDh.scale (-1)).eval i ∧
      (p.dh code).eval i = ((cond (Nat.ble 6 code) (p.Dh - i*p.dDh) 0 : ℕ) : ℤ) := by
    by_cases hc : 6 ≤ code
    · have hb : Nat.ble 6 code = true := Nat.ble_eq_true_of_le hc
      rw [hb] at hD
      have hD' : i*p.dDh ≤ p.Dh := by simpa only [cond, Nat.ble_eq] using hD
      have e := affine_cast p.Dh p.dDh i hD'
      rw [hb]
      simp only [Input.dh, if_pos hc, Input.atDh, cond, e]
      exact ⟨Int.natCast_nonneg _, trivial⟩
    · have hb : Nat.ble 6 code = false := Bool.eq_false_iff.mpr (fun hb => hc (Nat.le_of_ble_eq_true hb))
      rw [hb] at hD
      have hD' : p.Dh ≤ i*p.dDh := by simpa only [cond, Nat.ble_eq] using hD
      rw [hb]
      simp only [Input.dh, if_neg hc, Input.atDh, Affine.scale, Affine.eval, cond]
      refine ⟨?_, by simp⟩
      have hc' : ((p.Dh : ℕ) : ℤ) ≤ (i : ℤ)*(p.dDh : ℤ) := by exact_mod_cast hD'
      linarith
  obtain ⟨hDz, edh⟩ := key
  generalize cond (Nat.ble 6 code) (p.Dh - i*p.dDh) 0 = dh at edh h1 h2 h3 h4 h5
  have eu : (p.u code).eval i =
      ((cond (Nat.beq (code/2%3) 0) (131071*t) (cond (Nat.beq (code/2%3) 1) (131071*y) (dh+s)) : ℕ) : ℤ) := by
    rcases (show code/2%3 = 0 ∨ code/2%3 = 1 ∨ code/2%3 = 2 by omega) with hm | hm | hm <;>
      simp only [Input.u, hm, Affine.eval_scale, Affine.eval_add, et, ey, es, edh, cond, Nat.beq,
        if_true, if_false, one_ne_zero, OfNat.ofNat_ne_zero, OfNat.ofNat_ne_one] <;> push_cast <;> ring
  generalize cond (Nat.beq (code/2%3) 0) (131071*t) (cond (Nat.beq (code/2%3) 1) (131071*y) (dh+s)) = u
    at eu h1 h2 h3 h4 h5
  have ec : (p.c code).eval i = ((cond (Nat.beq (code%2) 0) (131071*s) u : ℕ) : ℤ) := by
    rcases (show code%2 = 0 ∨ code%2 = 1 by omega) with hm | hm <;>
      simp only [Input.c, hm, Affine.eval_scale, es, eu, cond, Nat.beq, if_true, if_false,
        one_ne_zero] <;> push_cast <;> ring
  generalize cond (Nat.beq (code%2) 0) (131071*s) u = c at ec h4 h5
  simp only [FastValidAt]
  rw [et, ey, es, eu, ec, edh]
  exact ⟨Int.natCast_nonneg _, Int.natCast_nonneg _, Int.natCast_nonneg _, hDz,
    by exact_mod_cast h1, by exact_mod_cast h2, by exact_mod_cast h3, by exact_mod_cast h4,
    by exact_mod_cast h5⟩

def runsValidK (p : Input) (runs : List Run) : ℕ → Bool :=
  List.rec (motive := fun _ => ℕ → Bool) (fun start => Nat.beq start p.fuel)
    (fun run _ ih start => Bool.rec false (ih run.stop)
      (Nat.blt start run.stop && Nat.ble run.stop p.fuel &&
        validN p run.code start && validN p run.code (run.stop-1))) runs

theorem runsValidK_sound (p : Input) (runs : List Run) (start : ℕ)
    (h : runsValidK p runs start = true) : RunsValid p start runs := by
  induction runs generalizing start with
  | nil => exact Nat.eq_of_beq_eq_true h
  | cons run runs ih =>
    change Bool.rec false (runsValidK p runs run.stop) (Nat.blt start run.stop &&
      Nat.ble run.stop p.fuel && validN p run.code start && validN p run.code (run.stop-1)) = true at h
    cases hb : (Nat.blt start run.stop && Nat.ble run.stop p.fuel &&
        validN p run.code start && validN p run.code (run.stop-1)) with
    | false => rw [hb] at h; exact absurd h Bool.false_ne_true
    | true =>
      rw [hb] at h
      simp only [Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq] at hb
      exact ⟨⟨hb.1.1.1, hb.1.1.2, validN_sound _ _ _ hb.1.2, validN_sound _ _ _ hb.2⟩, ih _ h⟩

def sPow (x : ℕ) : ℕ × ℕ × ℕ × ℕ :=
  let xx1 := x*(x-1)
  (12*x, 6*xx1, 2*xx1*(2*x-1), 3*(xx1*xx1))

theorem sPow_mono {lo hi : ℕ} (h : lo ≤ hi) :
    (sPow lo).1 ≤ (sPow hi).1 ∧ (sPow lo).2.1 ≤ (sPow hi).2.1 ∧
      (sPow lo).2.2.1 ≤ (sPow hi).2.2.1 ∧ (sPow lo).2.2.2 ≤ (sPow hi).2.2.2 := by
  have h1 : lo*(lo-1) ≤ hi*(hi-1) := Nat.mul_le_mul h (Nat.sub_le_sub_right h 1)
  have h2 : 2*lo-1 ≤ 2*hi-1 := Nat.sub_le_sub_right (Nat.mul_le_mul_left 2 h) 1
  simp only [sPow]
  refine ⟨Nat.mul_le_mul_left 12 h, Nat.mul_le_mul_left 6 h1, Nat.mul_le_mul (Nat.mul_le_mul_left 2 h1) h2,
    Nat.mul_le_mul_left 3 (Nat.mul_le_mul h1 h1)⟩

theorem factoredBoxPrefix_sPow (a b c : Affine) (n : ℕ) :
    factoredBoxPrefix a b c n =
      let w : ℤ := 131071
      let A := a.constant
      let B := b.constant
      let C := c.constant
      let α := a.slope
      let β := b.slope
      let γ := c.slope
      let q0 := (C+2*w)*(3*A+3*w+C)+B*(6*A+9*w+3*C+3*B)
      let q1 := γ*(3*A+5*w+2*C+3*B)+α*(3*C+6*w+6*B)+β*(6*A+9*w+3*C+6*B)
      let q2 := γ*(3*α+γ+3*β)+β*(6*α+3*β)
      (C+w)*(q0*(sPow n).1+q1*(sPow n).2.1+q2*(sPow n).2.2.1)+
        γ*(q0*(sPow n).2.1+q1*(sPow n).2.2.1+q2*(sPow n).2.2.2) := by
  unfold factoredBoxPrefix sPow
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · rw [if_neg (by omega)]
    have h1 : ((n-1 : ℕ) : ℤ) = (n : ℤ)-1 := by push_cast [Nat.cast_sub hn]; ring
    have h2 : ((2*n-1 : ℕ) : ℤ) = 2*(n : ℤ)-1 := by push_cast [Nat.cast_sub (by omega : 1 ≤ 2*n)]; ring
    simp only [Nat.cast_mul, Nat.cast_ofNat, h1, h2]
    ring

def runUpperK (p : Input) (start : ℕ) (run : Run) : ℤ :=
  let a := p.a run.code
  let b := p.b run.code
  let c := p.c run.code
  let w : ℤ := 131071
  let A := a.constant
  let B := b.constant
  let C := c.constant
  let α := a.slope
  let β := b.slope
  let γ := c.slope
  let q0 := (C+2*w)*(3*A+3*w+C)+B*(6*A+9*w+3*C+3*B)
  let q1 := γ*(3*A+5*w+2*C+3*B)+α*(3*C+6*w+6*B)+β*(6*A+9*w+3*C+6*B)
  let q2 := γ*(3*α+γ+3*β)+β*(6*α+3*β)
  let hi := sPow run.stop
  let lo := sPow start
  let d0 : ℤ := ((hi.1-lo.1 : ℕ) : ℤ)
  let d1 : ℤ := ((hi.2.1-lo.2.1 : ℕ) : ℤ)
  let d2 : ℤ := ((hi.2.2.1-lo.2.2.1 : ℕ) : ℤ)
  let d3 : ℤ := ((hi.2.2.2-lo.2.2.2 : ℕ) : ℤ)
  (C+w)*(q0*d0+q1*d1+q2*d2)+γ*(q0*d1+q1*d2+q2*d3)

theorem runUpperK_eq (p : Input) (start : ℕ) (run : Run) (h : start ≤ run.stop) :
    runUpperK p start run = runUpper p start run := by
  obtain ⟨m0, m1, m2, m3⟩ := sPow_mono h
  unfold runUpperK runUpper
  rw [factoredBoxPrefix_sPow, factoredBoxPrefix_sPow]
  simp only [Nat.cast_sub m0, Nat.cast_sub m1, Nat.cast_sub m2, Nat.cast_sub m3]
  ring

def runsUpperK (p : Input) (runs : List Run) : ℕ → ℤ :=
  List.rec (motive := fun _ => ℕ → ℤ) (fun _ => 0)
    (fun run _ ih start => runUpperK p start run + ih run.stop) runs

theorem runsUpperK_eq (p : Input) (runs : List Run) (start : ℕ) (h : RunsValid p start runs) :
    runsUpperK p runs start = runsUpper p start runs := by
  induction runs generalizing start with
  | nil => rfl
  | cons run runs ih =>
    change runUpperK p start run + runsUpperK p runs run.stop = runUpper p start run + runsUpper p run.stop runs
    rw [runUpperK_eq p start run h.1.1.le, ih run.stop h.2]

def zlt (a b : ℤ) : Bool := Int.casesOn (motive := fun _ => Bool) (b - a) (fun k => Nat.ble 1 k) (fun _ => false)

theorem zlt_sound (a b : ℤ) (h : zlt a b = true) : a < b := by
  unfold zlt at h
  rcases hb : b - a with k | k <;> rw [hb] at h
  · have hk : 1 ≤ k := Nat.le_of_ble_eq_true h
    rw [Int.ofNat_eq_natCast] at hb
    omega
  · exact absurd h Bool.false_ne_true

def sufficientK (s : SourceNumbers) (r v threshold : ℕ) (runs : List Run) : Bool :=
  Nat.blt (11192-(r+v)) threshold ||
    (let p := rawFlag r v threshold
     Nat.ble 1 p.all && Nat.ble (total p) s.totalCap && Nat.ble (middle p) s.middleCap &&
       Nat.ble p.all s.slopeCap && runsValidK (ofSource s p) runs 0 &&
       zlt (50175*runsUpperK (ofSource s p) runs 0) ((s.gap*162125875761905592 : ℕ) : ℤ))

theorem sufficientK_sound (s : SourceNumbers) (r v threshold : ℕ) (runs : List Run)
    (h : sufficientK s r v threshold runs = true) : Sufficient s r v threshold runs := by
  simp only [sufficientK, Bool.or_eq_true, Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq] at h
  rcases h with h | ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩
  · exact Or.inl h
  · have hv := runsValidK_sound _ _ _ h5
    refine Or.inr ⟨h1, h2, h3, h4, hv, ?_⟩
    have hz := zlt_sound _ _ h6
    rw [runsUpperK_eq _ _ _ hv] at hz
    push_cast at hz
    norm_num
    linarith

def thresholdK (s : SourceNumbers) (r v threshold : ℕ) (runs : List Run) : Bool :=
  sufficientK s r v threshold runs || fastK s r v threshold

theorem thresholdK_sound (s : SourceNumbers) (r v threshold : ℕ) (runs : List Run)
    (h : thresholdK s r v threshold runs = true) :
    FastSourceThresholdSufficient s r v threshold := by
  simp only [thresholdK, Bool.or_eq_true] at h
  rcases h with h | h
  · exact Lower80899.CompressedBand.sufficient_sound s r v threshold runs (sufficientK_sound _ _ _ _ _ h)
  · exact fastK_sound _ _ _ _ h

end ProximityPrize.SubmissionLower.FinalThreshold6815
end MergedPart2
section MergedPart3
namespace ProximityPrize.SubmissionLower.RelativeBounded6814
open scoped BigOperators
open MvPolynomial RCN119 RCN100 RCN122 ContactOrderBridge
open RelativeContactOrder6814
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
variable (K : Type*) [Field K]

theorem regular_contact_mass
    {I : Type*} (F : Poly4 K) (hF : F ≠ 0) (f : Polynomial K) (gamma : K)
    (nodes : I ↪ K) (u0 u1 : I → K) (support : Finset I) (w nu : ℕ)
    (hdegree : f.natDegree ≤ w)
    (hweight : MvPolynomial.weightedTotalDegree (RCN081.contactWeights w) F ≤ nu)
    (hregular : specialization K f gamma (MvPolynomial.pderiv (2 : Fin 4) F) ≠ 0)
    (hagrees : ∀ i ∈ support, f.eval (nodes i) = u0 i+gamma*u1 i) :
    (∑ i ∈ support, (contactOrder K (nodes i) (u0 i) (u1 i) F-1)) + w ≤ nu+1 := by
  classical
  let H := MvPolynomial.pderiv (2 : Fin 4) F
  let P := specialization K f gamma H
  have hmult : ∀ i ∈ support,
      contactOrder K (nodes i) (u0 i) (u1 i) F-1 ≤ P.rootMultiplicity (nodes i) := by
    intro i hi
    have hc : ContactAtLeast K (nodes i) (u0 i) (u1 i)
        (contactOrder K (nodes i) (u0 i) (u1 i) F) F :=
      (contactAtLeast_iff_le K _ _ _ _ F hF).mpr le_rfl
    have hd := contactAtLeast_pderiv_R K (nodes i) (u0 i) (u1 i) _ F hc
    have ht := X_pow_dvd_taylor_specialization K H f (nodes i) (u0 i) (u1 i) gamma _
      (hagrees i hi) ((contactAtLeast_iff_block_divisibility K _ _ _ _ H).mp hd)
    apply (Polynomial.le_rootMultiplicity_iff hregular).mpr
    exact (RCN185.shifted_power_dvd_iff_taylor_coeff_zero P (nodes i) _).mpr
      (Polynomial.X_pow_dvd_iff.mp ht)
  have hs : (∑ i ∈ support, (contactOrder K (nodes i) (u0 i) (u1 i) F-1)) ≤ P.natDegree := by
    calc
      _ ≤ ∑ i ∈ support, P.rootMultiplicity (nodes i) := Finset.sum_le_sum hmult
      _ = ∑ a ∈ support.map nodes, P.rootMultiplicity a :=
        (Finset.sum_map support nodes (fun a : K => P.rootMultiplicity a)).symm
      _ ≤ _ := @RCN355.sum_rootMultiplicity_le_natDegree K inferInstance (Classical.decEq K)
        P (support.map nodes)
  have hd := specialized_R_derivative_degree K F f gamma w nu hdegree hweight hregular
  change P.natDegree+w ≤ nu+1 at hd
  omega

theorem affine_order_mass {I : Type*} (support : Finset I) (d : I → ℕ)
    (alpha beta A H : ℕ) (hcard : A ≤ support.card) (hmass : (∑ i ∈ support, d i) ≤ H) :
    alpha*A-beta*H ≤ ∑ i ∈ support, (alpha-beta*d i) := by
  classical
  have hsum : alpha*support.card ≤
      (∑ i ∈ support, (alpha-beta*d i)) + beta*(∑ i ∈ support, d i) := by
    calc
      _ = ∑ _i ∈ support, alpha := by simp [Nat.mul_comm]
      _ ≤ ∑ i ∈ support, ((alpha-beta*d i)+beta*d i) :=
        Finset.sum_le_sum fun i _ => by omega
      _ = _ := by rw [Finset.sum_add_distrib, Finset.mul_sum]
  have hc := Nat.mul_le_mul_left alpha hcard
  have hm := Nat.mul_le_mul_left beta hmass
  omega

end
end ProximityPrize.SubmissionLower.RelativeBounded6814
end MergedPart3
section MergedPart4
namespace ProximityPrize.SubmissionLower.RelativeBounded6814
open scoped BigOperators
open MvPolynomial RCN119 RCN100 RCN122 ContactOrderBridge
open RelativeContactOrder6814
open RCN234 (wt)
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
variable (K : Type*) [Field K]
local instance : DecidableEq K := Classical.decEq K

end
end ProximityPrize.SubmissionLower.RelativeBounded6814
end MergedPart4
section MergedPart5
namespace ProximityPrize.SubmissionLower.RelativeBounded6814
open scoped BigOperators
open MvPolynomial RCN119 RCN100 RCN122 ContactOrderBridge
open RelativeContactOrder6814 RelativeContactRank6814
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
variable (K : Type*) [Field K]

theorem homogenized_zero_eq (F : Poly4 K) :
    homogenizedTranslation K 0 0 0 F =
      MvPolynomial.finSuccEquiv K 3 (contactBlowup K F) := by
  have hX1 : MvPolynomial.finSuccEquiv K 3 (MvPolynomial.X (1 : Fin 4)) =
      Polynomial.C (MvPolynomial.X (0 : Fin 3)) := MvPolynomial.finSuccEquiv_X_succ (j:=(0 : Fin 3))
  have hX2 : MvPolynomial.finSuccEquiv K 3 (MvPolynomial.X (2 : Fin 4)) =
      Polynomial.C (MvPolynomial.X (1 : Fin 3)) := MvPolynomial.finSuccEquiv_X_succ (j:=(1 : Fin 3))
  have hX3 : MvPolynomial.finSuccEquiv K 3 (MvPolynomial.X (3 : Fin 4)) =
      Polynomial.C (MvPolynomial.X (2 : Fin 3)) := MvPolynomial.finSuccEquiv_X_succ (j:=(2 : Fin 3))
  have hgen (i : Fin 4) :
      homogenizedTranslation K 0 0 0 (MvPolynomial.X i) =
        MvPolynomial.finSuccEquiv K 3 (contactBlowup K (MvPolynomial.X i)) := by
    rw [contactBlowup_X]
    fin_cases i <;> simp [homogenizedTranslation,translationVariables,seedAffine,
      MvPolynomial.finSuccEquiv_X_zero,hX1,hX2,hX3]
  induction F using MvPolynomial.induction_on with
  | C a => simp [homogenizedTranslation, MvPolynomial.finSuccEquiv_apply,
      Polynomial.algebraMap_apply,MvPolynomial.algebraMap_eq]
  | add F G hF hG => simp only [map_add,hF,hG]
  | mul_X F i hF => simpa only [map_mul] using congrArg₂ (· * ·) hF (hgen i)

theorem translated_zero_coeff (F : Poly4 K) (d : Fin 4 →₀ ℕ) :
    MvPolynomial.coeff d.tail
        ((homogenizedTranslation K 0 0 0 F).coeff (d 0+d 1)) = MvPolynomial.coeff d F := by
  rw [homogenized_zero_eq, MvPolynomial.finSuccEquiv_coeff_coeff]
  have he : Finsupp.cons (d 0+d 1) d.tail = blowupExponent d := by
    ext i
    fin_cases i <;> simp [blowupExponent] <;> rfl
  rw [he]
  change Finsupp.mapDomain blowupExponent (AddMonoidAlgebra.coeff F) (blowupExponent d) = _
  exact Finsupp.mapDomain_apply blowupExponent_injective _ _

theorem X_dvd_of_contact_large {DF T R B : ℕ} (F : Poly4 K)
    (hbox : F ∈ globalCoefficientBox K DF 1 T R) (hY : F.degreeOf 1 ≤ B)
    (hcontact : ContactAtLeast K 0 0 0 (B+R+1) F) :
    MvPolynomial.X (0 : Fin 4) ∣ F := by
  classical
  let m := B+R+1
  have hz (n : ℕ) (hn : n ≤ B) : (homogenizedTranslation K 0 0 0 F).coeff n = 0 := by
    have hnm : n < m := by dsimp [m]; omega
    let p := blocksOf K m (⟨F,hbox⟩ : globalCoefficientBox K DF 1 T R) ⟨n,hnm⟩
    have hp : (blockJet K (min n T) T R (m-n)) p = 0 := by
      change contactJet K (m-n) p.val = 0
      apply (contactJet_eq_zero_iff K (m-n) _).mpr
      rw [blocksOf_coeff]
      exact (contactAtLeast_iff_block_divisibility K 0 0 0 m F).mp hcontact n
    have hker : p ∈ LinearMap.ker (blockJet K (min n T) T R (m-n)) := hp
    rw [blockJet_kernel_eq_bot_of_large K (min n T) T R (m-n)
      (Or.inr (by dsimp [m]; omega))] at hker
    have hp0 : p = 0 := by simpa using hker
    have he := congrArg Subtype.val hp0
    rw [blocksOf_coeff] at he
    exact he
  have hc (d : Fin 4 →₀ ℕ) (hd : d 0 = 0) : MvPolynomial.coeff d F = 0 := by
    by_contra hne
    have hd1 := MvPolynomial.degreeOf_le_iff.mp hY d (MvPolynomial.mem_support_iff.mpr hne)
    have he := translated_zero_coeff K F d
    rw [hd,zero_add,hz (d 1) hd1,MvPolynomial.coeff_zero] at he
    exact hne he.symm
  have hdiv : Polynomial.X ∣ MvPolynomial.finSuccEquiv K 3 F := by
    apply Polynomial.X_dvd_iff.mpr
    ext d
    rw [MvPolynomial.finSuccEquiv_coeff_coeff, MvPolynomial.coeff_zero]
    exact hc (Finsupp.cons 0 d) rfl
  obtain ⟨Q,hQ⟩ := hdiv
  refine ⟨(MvPolynomial.finSuccEquiv K 3).symm Q,?_⟩
  apply (MvPolynomial.finSuccEquiv K 3).injective
  simpa only [map_mul,MvPolynomial.finSuccEquiv_X_zero,AlgEquiv.apply_symm_apply] using hQ

theorem contactOrder_le_of_X_not_dvd {DF T R B : ℕ} (F : Poly4 K) (hF : F ≠ 0)
    (hbox : F ∈ globalCoefficientBox K DF 1 T R) (hY : F.degreeOf 1 ≤ B)
    (hX : ¬ MvPolynomial.X (0 : Fin 4) ∣ F) : contactOrder K 0 0 0 F ≤ B+R := by
  by_contra h
  apply hX
  apply X_dvd_of_contact_large K F hbox hY
  exact (contactAtLeast_iff_le K 0 0 0 (B+R+1) F hF).mpr (by omega)

def centerEquiv (x u0 u1 : K) : Poly4 K ≃ₐ[K] Poly4 K :=
  AlgEquiv.ofAlgHom (center K x u0 u1) (center K (-x) (-u0) (-u1))
    (by
      apply DFunLike.ext
      intro Q
      change center K x u0 u1 (center K (-x) (-u0) (-u1) Q) = Q
      simpa using center_inverse K (-x) (-u0) (-u1) Q)
    (by
      apply DFunLike.ext
      intro Q
      exact center_inverse K x u0 u1 Q)

theorem X_not_dvd_center_of_irreducible (F : Poly4 K) (hF : Irreducible F)
    (hR : 0 < F.degreeOf 2) (x u0 u1 : K) :
    ¬ MvPolynomial.X (0 : Fin 4) ∣ center K x u0 u1 F := by
  intro hdiv
  let E := centerEquiv K (-x) (-u0) (-u1)
  have hp : Irreducible (E (MvPolynomial.X (0 : Fin 4))) :=
    (MulEquiv.irreducible_iff (f:=E.toMulEquiv)).mpr (MvPolynomial.X_prime.irreducible)
  have hd : E (MvPolynomial.X (0 : Fin 4)) ∣ F := by
    have hm := map_dvd E.toRingHom hdiv
    change center K (-x) (-u0) (-u1) (MvPolynomial.X (0 : Fin 4)) ∣
      center K (-x) (-u0) (-u1) (center K x u0 u1 F) at hm
    rw [center_inverse] at hm
    exact hm
  have hd' := (hp.associated_of_dvd hF hd).symm.dvd
  have hle := RCN081.degreeOf_le_of_dvd (2 : Fin 4) F _ hd' hp.ne_zero
  have he : E (MvPolynomial.X (0 : Fin 4)) = MvPolynomial.X 0+MvPolynomial.C (-x) := by
    simp [E,centerEquiv,center]
  rw [he] at hle
  have hh := MvPolynomial.degreeOf_add_le (2 : Fin 4)
    (MvPolynomial.X 0 : Poly4 K) (MvPolynomial.C (-x))
  have hh0 : (MvPolynomial.X 0+MvPolynomial.C (-x) : Poly4 K).degreeOf 2 ≤ 0 := by
    simpa [MvPolynomial.degreeOf_X] using hh
  omega

theorem contactOrder_le_middle_add_slope {DF T R B : ℕ} (F : Poly4 K)
    (hF : Irreducible F) (hR : 0 < F.degreeOf 2)
    (hbox : F ∈ globalCoefficientBox K DF 1 T R)
    (hB : RCN234.wt RCN156.residualYSWeights F ≤ B) (x u0 u1 : K) :
    contactOrder K x u0 u1 F ≤ B+R := by
  rw [← center_contactOrder K x u0 u1 F hF.ne_zero]
  apply contactOrder_le_of_X_not_dvd K (center K x u0 u1 F)
    (center_ne_zero K x u0 u1 hF.ne_zero) (center_globalBox K x u0 u1 ⟨F,hbox⟩)
  · apply MvPolynomial.degreeOf_le_iff.mpr
    intro d hd
    have hw := (MvPolynomial.le_weightedTotalDegree RCN156.residualYSWeights hd).trans
      ((center_weight_le K x u0 u1 RCN156.residualYSWeights (by decide) F).trans hB)
    rw [RCN081.weight_fin4] at hw
    simp only [RCN156.residualYSWeights] at hw
    simp at hw
    omega
  · exact X_not_dvd_center_of_irreducible K F hF hR x u0 u1

end
end ProximityPrize.SubmissionLower.RelativeBounded6814
end MergedPart5
section MergedPart6
namespace ProximityPrize.SubmissionLower.RelativeBounded6814
open scoped BigOperators
open MvPolynomial RCN119 RCN100 RCN122 ContactOrderBridge
open RelativeContactOrder6814
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
variable (K : Type*) [Field K]

theorem clipped_affine_order_mass {I : Type*} (support : Finset I) (d : I → ℕ)
    (alpha beta A H cap : ℕ) (hcard : A ≤ support.card)
    (hmass : (∑ i ∈ support, d i) ≤ H) (hcap : ∀ i ∈ support, d i ≤ cap) :
    alpha*A-beta*min H (cap*A) ≤ ∑ i ∈ support, (alpha-beta*d i) := by
  classical
  by_cases hh : H ≤ cap*A
  · rw [Nat.min_eq_left hh]
    exact affine_order_mass support d alpha beta A H hcard hmass
  · rw [Nat.min_eq_right (by omega : cap*A ≤ H)]
    calc
      alpha*A-beta*(cap*A) = (alpha-beta*cap)*A := by rw [Nat.sub_mul,Nat.mul_assoc]
      _ ≤ (alpha-beta*cap)*support.card := Nat.mul_le_mul_left _ hcard
      _ = ∑ _i ∈ support, (alpha-beta*cap) := by simp [Nat.mul_comm]
      _ ≤ _ := Finset.sum_le_sum fun i hi =>
        Nat.sub_le_sub_left (Nat.mul_le_mul_left beta (hcap i hi)) alpha

theorem regular_clipped_order_mass
    {I : Type*} {DF T R B : ℕ} (F : Poly4 K) (hF : Irreducible F)
    (hR : 0 < F.degreeOf 2) (hbox : F ∈ globalCoefficientBox K DF 1 T R)
    (hB : RCN234.wt RCN156.residualYSWeights F ≤ B)
    (f : Polynomial K) (gamma : K) (nodes : I ↪ K) (u0 u1 : I → K)
    (support : Finset I) (w nu alpha beta A : ℕ)
    (hnu : w ≤ nu) (hdegree : f.natDegree ≤ w)
    (hweight : MvPolynomial.weightedTotalDegree (RCN081.contactWeights w) F ≤ nu)
    (hregular : specialization K f gamma (MvPolynomial.pderiv (2 : Fin 4) F) ≠ 0)
    (hagrees : ∀ i ∈ support, f.eval (nodes i) = u0 i+gamma*u1 i)
    (hcard : A ≤ support.card) :
    alpha*A-beta*min (nu-w+1) ((B+R-1)*A) ≤
      ∑ i ∈ support, (alpha-beta*(contactOrder K (nodes i) (u0 i) (u1 i) F-1)) := by
  have hm := regular_contact_mass K F hF.ne_zero f gamma nodes u0 u1 support w nu
    hdegree hweight hregular hagrees
  apply clipped_affine_order_mass support _ alpha beta A (nu-w+1) (B+R-1) hcard
  · omega
  · intro i _
    exact Nat.sub_le_sub_right
      (contactOrder_le_middle_add_slope K F hF hR hbox hB (nodes i) (u0 i) (u1 i)) 1

end
end ProximityPrize.SubmissionLower.RelativeBounded6814
end MergedPart6
section MergedPart7
namespace ProximityPrize.SubmissionLower.RelativeBounded6814
open scoped BigOperators
open MvPolynomial RCN119 RCN100 RCN122 ContactOrderBridge
open RelativeContactOrder6814
open RCN234 (wt)
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
variable (K : Type*) [Field K]
local instance : DecidableEq K := Classical.decEq K

def profileRowRank (alpha beta L s T R mu : ℕ) : ℕ :=
  localRankBound (alpha-beta*(mu-1)) L s-
    localRankBound (alpha-beta*(mu-1)-mu) (L-T) (s-R)

theorem profile_dimension_test
    {I : Type*} [Fintype I] {DF T R B D w L s nu : ℕ}
    (F : Poly4 K) (hF : Irreducible F) (hR : 0 < F.degreeOf 2)
    (hbox : F ∈ globalCoefficientBox K DF 1 T R)
    (hB : wt RCN156.residualYSWeights F ≤ B)
    (nodes u0 u1 : I → K) (alpha beta : ℕ)
    (hrows : ∀ mu ≤ B+R, coefficientCount (D-nu) w (L-T) (s-R) +
      Fintype.card I*profileRowRank alpha beta L s T R mu < coefficientCount D w L s) :
    coefficientCount (D-nu) w (L-T) (s-R) +
      (∑ i : I, profileRowRank alpha beta L s T R
        (contactOrder K (nodes i) (u0 i) (u1 i) F)) < coefficientCount D w L s := by
  classical
  let rows := Finset.range (B+R+1)
  have hn : rows.Nonempty := ⟨0,by simp [rows]⟩
  obtain ⟨mu,hmu,heq⟩ := Finset.exists_mem_eq_sup rows hn (profileRowRank alpha beta L s T R)
  have hbound (i : I) : profileRowRank alpha beta L s T R
      (contactOrder K (nodes i) (u0 i) (u1 i) F) ≤
        rows.sup (profileRowRank alpha beta L s T R) := by
    apply Finset.le_sup
    have hc := contactOrder_le_middle_add_slope K F hF hR hbox hB (nodes i) (u0 i) (u1 i)
    simpa [rows] using (show contactOrder K (nodes i) (u0 i) (u1 i) F < B+R+1 by omega)
  have hs : (∑ i : I, profileRowRank alpha beta L s T R
      (contactOrder K (nodes i) (u0 i) (u1 i) F)) ≤
        Fintype.card I*rows.sup (profileRowRank alpha beta L s T R) := by
    calc
      _ ≤ ∑ _i : I, rows.sup (profileRowRank alpha beta L s T R) :=
        Finset.sum_le_sum fun i _ => hbound i
      _ = _ := by simp
  have hc := hrows mu (by have := Finset.mem_range.mp hmu; omega)
  rw [heq] at hs
  exact (Nat.add_le_add_left hs _).trans_lt hc

theorem exists_profile_helper
    {I : Type*} [Fintype I] [DecidableEq I] {DF T R B D w L s nu : ℕ}
    (F : Poly4 K) (hF : Irreducible F) (hRpos : 0 < F.degreeOf 2)
    (hbox : F ∈ globalCoefficientBox K DF 1 T R) (hT : T ≤ L) (hR : R ≤ s)
    (hcode : wt (RCN081.contactWeights w) F = nu)
    (htotal : T ≤ wt RCN156.residualTotalWeights F)
    (hslope : R ≤ wt RCN156.residualSWeights F)
    (hB : wt RCN156.residualYSWeights F ≤ B)
    (nodes : I ↪ K) (u0 u1 : I → K) (alpha beta A : ℕ) (hnu : w ≤ nu)
    (hDpos : 0 < D) (hD : D ≤ alpha*A-beta*min (nu-w+1) ((B+R-1)*A))
    (hrows : ∀ mu ≤ B+R, coefficientCount (D-nu) w (L-T) (s-R) +
      Fintype.card I*profileRowRank alpha beta L s T R mu < coefficientCount D w L s)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ w)
    (hsolution : ∀ gamma ∈ Gamma, specialization K (selected gamma) gamma F = 0)
    (hregular : ∀ gamma ∈ Gamma,
      specialization K (selected gamma) gamma (MvPolynomial.pderiv (2 : Fin 4) F) ≠ 0)
    (hagreement : ∀ gamma ∈ Gamma, A ≤
      ((Finset.univ : Finset I).filter
        (fun i => (selected gamma).eval (nodes i) = u0 i+gamma*u1 i)).card) :
    ∃ Q : Poly4 K, Q ∈ globalCoefficientBox K D w L s ∧ IsRelPrime F Q ∧
      ∀ gamma ∈ Gamma, specialization K (selected gamma) gamma Q = 0 := by
  classical
  let m : I → ℕ := fun i => alpha-beta*(contactOrder K (nodes i) (u0 i) (u1 i) F-1)
  have hd := profile_dimension_test K F hF hRpos hbox hB nodes u0 u1 alpha beta hrows
  obtain ⟨Q,hQ,hproper,hcontact⟩ := exists_proper_relative_helper K F hF.ne_zero hbox hT hR
    hcode.symm.le htotal hslope nodes u0 u1 m hd
  refine ⟨Q,hQ,hF.isRelPrime_iff_not_dvd.mpr hproper,?_⟩
  intro gamma hgamma
  let support := (Finset.univ : Finset I).filter
    (fun i => (selected gamma).eval (nodes i) = u0 i+gamma*u1 i)
  have hv : ∀ i ∈ support, (selected gamma).eval (nodes i) = u0 i+gamma*u1 i := by
    intro i hi
    exact (Finset.mem_filter.mp hi).2
  have hmass := regular_clipped_order_mass K F hF hRpos hbox hB (selected gamma) gamma
    nodes u0 u1 support w nu alpha beta A hnu (hdegree gamma hgamma) hcode.le
    (hregular gamma hgamma) hv (hagreement gamma hgamma)
  apply relative_contact_specialization_eq_zero K F Q (selected gamma) gamma nodes u0 u1 support m
    (hsolution gamma hgamma) hv (fun i _ => hcontact i)
  exact (specialization_natDegree_lt K D w L s Q (selected gamma) gamma hDpos hQ
    (hdegree gamma hgamma)).trans_le (hD.trans hmass)

end
end ProximityPrize.SubmissionLower.RelativeBounded6814
end MergedPart7
section MergedPart8
namespace ProximityPrize.SubmissionLower.RelativeBounded6814
open scoped BigOperators
open RCN100
set_option autoImplicit false
set_option maxHeartbeats 2000000

theorem coefficientCount_mono_cutoff (w L s : ℕ) :
    Monotone (fun D => coefficientCount D w L s) := by
  intro D1 D2 hD
  unfold coefficientCount
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  apply Nat.mul_le_mul_left
  exact Nat.sub_le_sub_right (Nat.sub_le_sub_right hD _) _

theorem profile_rows_mono_weight {D w L s T R B N alpha beta lo nu : ℕ}
    (hnu : lo ≤ nu)
    (hrows : ∀ mu ≤ B+R, coefficientCount (D-lo) w (L-T) (s-R) +
      N*profileRowRank alpha beta L s T R mu < coefficientCount D w L s) :
    ∀ mu ≤ B+R, coefficientCount (D-nu) w (L-T) (s-R) +
      N*profileRowRank alpha beta L s T R mu < coefficientCount D w L s := by
  intro mu hmu
  have hcoef := coefficientCount_mono_cutoff w (L-T) (s-R)
    (Nat.sub_le_sub_left hnu D)
  exact (Nat.add_le_add_right hcoef _).trans_lt (hrows mu hmu)

theorem clipped_cutoff_antitone (alpha beta w B R A : ℕ) :
    Antitone (fun nu => alpha*A-beta*min (nu-w+1) ((B+R-1)*A)) := by
  intro lo hi h
  apply Nat.sub_le_sub_left
  apply Nat.mul_le_mul_left
  exact min_le_min (Nat.add_le_add_right (Nat.sub_le_sub_right h w) 1) le_rfl

end ProximityPrize.SubmissionLower.RelativeBounded6814
end MergedPart8
section MergedPart9
namespace ProximityPrize.SubmissionLower.RelativeBounded6814
open scoped BigOperators
open RCN100
set_option autoImplicit false

theorem hinge_tangent (D x c : ℕ) (h : D ≤ x) :
    (D-c)+((D+1-c)-(D-c))*(x-D) ≤ x-c := by
  by_cases hc : c ≤ D
  · have h1 : (D+1-c)-(D-c) = 1 := by omega
    rw [h1, one_mul]
    omega
  · have h1 : (D+1-c)-(D-c) = 0 := by omega
    rw [h1, zero_mul]
    omega

theorem hinge_chord (a x b c : ℕ) (hax : a ≤ x) (hxb : x ≤ b) :
    (b-a)*(x-c) ≤ (b-x)*(a-c)+(x-a)*(b-c) := by
  rcases Nat.lt_or_ge a c with hac | hca
  swap
  ·
    have hba : b-a = (b-x)+(x-a) := by omega
    have hx : x-c = (x-a)+(a-c) := by omega
    have hb : b-c = (b-x)+(x-a)+(a-c) := by omega
    rw [hba, hx, hb]
    apply le_of_eq
    ring
  rcases Nat.lt_or_ge x c with hxc | hcx
  swap
  ·
    have ha : a-c = 0 := by omega
    rw [ha, Nat.mul_zero, Nat.zero_add]
    have hb : b-c = (b-x)+(x-c) := by omega
    have hxa : x-a = (x-c)+(c-a) := by omega
    have hba : b-a = (b-x)+(x-c)+(c-a) := by omega
    rw [hb, hxa, hba]
    nlinarith [Nat.zero_le ((b-x)*(c-a))]
  · have hx : x-c = 0 := by omega
    rw [hx, Nat.mul_zero]
    exact Nat.zero_le _

theorem coefficientCount_eq_hinges (D w L s : ℕ) :
    coefficientCount D w L s =
      ∑ i ∈ Finset.range (L+1), ∑ j ∈ Finset.range (s+1),
        (L+1-i-j)*(D-(w*i+(w-1)*j)) := by
  unfold coefficientCount
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [Nat.sub_sub, Nat.sub_sub]

def countSlopeAt (D w L s : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (L+1), ∑ j ∈ Finset.range (s+1),
    (L+1-i-j)*((D+1-(w*i+(w-1)*j))-(D-(w*i+(w-1)*j)))

theorem coefficientCount_tangent (D x w L s : ℕ) (h : D ≤ x) :
    coefficientCount D w L s+countSlopeAt D w L s*(x-D) ≤ coefficientCount x w L s := by
  rw [coefficientCount_eq_hinges, coefficientCount_eq_hinges, countSlopeAt,
    Finset.sum_mul, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  rw [Finset.sum_mul, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro j _
  have ht := hinge_tangent D x (w*i+(w-1)*j) h
  calc (L+1-i-j)*(D-(w*i+(w-1)*j))+
        (L+1-i-j)*((D+1-(w*i+(w-1)*j))-(D-(w*i+(w-1)*j)))*(x-D)
      = (L+1-i-j)*((D-(w*i+(w-1)*j))+
          ((D+1-(w*i+(w-1)*j))-(D-(w*i+(w-1)*j)))*(x-D)) := by ring
    _ ≤ (L+1-i-j)*(x-(w*i+(w-1)*j)) := Nat.mul_le_mul_left _ ht

theorem coefficientCount_chord (a x b w L s : ℕ) (hax : a ≤ x) (hxb : x ≤ b) :
    (b-a)*coefficientCount x w L s ≤
      (b-x)*coefficientCount a w L s+(x-a)*coefficientCount b w L s := by
  rw [coefficientCount_eq_hinges, coefficientCount_eq_hinges, coefficientCount_eq_hinges,
    Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro j _
  have hc := hinge_chord a x b (w*i+(w-1)*j) hax hxb
  calc (b-a)*((L+1-i-j)*(x-(w*i+(w-1)*j)))
      = (L+1-i-j)*((b-a)*(x-(w*i+(w-1)*j))) := by ring
    _ ≤ (L+1-i-j)*((b-x)*(a-(w*i+(w-1)*j))+(x-a)*(b-(w*i+(w-1)*j))) :=
        Nat.mul_le_mul_left _ hc
    _ = (b-x)*((L+1-i-j)*(a-(w*i+(w-1)*j)))+(x-a)*((L+1-i-j)*(b-(w*i+(w-1)*j))) := by ring

theorem wide_rows_core (w L s T R K beta Dhi Ehi H t : ℕ) (ht : t ≤ H)
    (hHi : coefficientCount Ehi w (L-T) (s-R)+K < coefficientCount Dhi w L s)
    (hLo : coefficientCount (Ehi+(beta+1)*H) w (L-T) (s-R)+K <
      coefficientCount Dhi w L s+countSlopeAt Dhi w L s*(beta*H)) :
    coefficientCount (Ehi+(beta+1)*t) w (L-T) (s-R)+K < coefficientCount (Dhi+beta*t) w L s := by
  set G2 := fun E => coefficientCount E w (L-T) (s-R) with hG2
  set g1 := coefficientCount Dhi w L s
  set m := countSlopeAt Dhi w L s
  have htan := coefficientCount_tangent Dhi (Dhi+beta*t) w L s (Nat.le_add_right _ _)
  rw [Nat.add_sub_cancel_left] at htan
  rcases Nat.eq_zero_or_pos H with hH | hH
  · have : t = 0 := by omega
    subst this
    simpa using hHi

  have hch := coefficientCount_chord Ehi (Ehi+(beta+1)*t) (Ehi+(beta+1)*H) w (L-T) (s-R)
    (Nat.le_add_right _ _) (by have := Nat.mul_le_mul_left (beta+1) ht; omega)
  have e1 : Ehi+(beta+1)*H-Ehi = (beta+1)*H := by omega
  have e2 : Ehi+(beta+1)*H-(Ehi+(beta+1)*t) = (beta+1)*(H-t) := by
    rw [Nat.mul_sub]; omega
  have e3 : Ehi+(beta+1)*t-Ehi = (beta+1)*t := by omega
  rw [e1, e2, e3] at hch
  have hch' : H*G2 (Ehi+(beta+1)*t) ≤ (H-t)*G2 Ehi+t*G2 (Ehi+(beta+1)*H) := by
    have hpos : 0 < beta+1 := Nat.succ_pos _
    have : (beta+1)*(H*G2 (Ehi+(beta+1)*t)) ≤ (beta+1)*((H-t)*G2 Ehi+t*G2 (Ehi+(beta+1)*H)) := by
      calc (beta+1)*(H*G2 (Ehi+(beta+1)*t)) = (beta+1)*H*G2 (Ehi+(beta+1)*t) := by ring
        _ ≤ (beta+1)*(H-t)*G2 Ehi+(beta+1)*t*G2 (Ehi+(beta+1)*H) := hch
        _ = (beta+1)*((H-t)*G2 Ehi+t*G2 (Ehi+(beta+1)*H)) := by ring
    exact Nat.le_of_mul_le_mul_left this hpos

  have hsum : H*(G2 (Ehi+(beta+1)*t)+K) < H*(g1+m*(beta*t)) := by
    have hsplit : H = (H-t)+t := by omega
    rcases Nat.eq_zero_or_pos t with h0 | h0
    · subst h0
      simp only [Nat.mul_zero, Nat.add_zero, Nat.sub_zero] at hch' ⊢
      have := Nat.mul_lt_mul_of_pos_left hHi hH
      nlinarith [hch']
    · have hA : (H-t)*(G2 Ehi+K) ≤ (H-t)*g1 := Nat.mul_le_mul_left _ hHi.le
      have hB : t*(G2 (Ehi+(beta+1)*H)+K) < t*(g1+m*(beta*H)) := Nat.mul_lt_mul_of_pos_left hLo h0
      have hC : t*(m*(beta*H)) = H*(m*(beta*t)) := by ring
      calc H*(G2 (Ehi+(beta+1)*t)+K) = H*G2 (Ehi+(beta+1)*t)+H*K := by ring
        _ ≤ (H-t)*G2 Ehi+t*G2 (Ehi+(beta+1)*H)+((H-t)+t)*K := by
            rw [← hsplit]; exact Nat.add_le_add_right hch' _
        _ = (H-t)*(G2 Ehi+K)+t*(G2 (Ehi+(beta+1)*H)+K) := by ring
        _ < (H-t)*g1+t*(g1+m*(beta*H)) := Nat.add_lt_add_of_le_of_lt hA hB
        _ = ((H-t)+t)*g1+t*(m*(beta*H)) := by ring
        _ = H*(g1+m*(beta*t)) := by rw [← hsplit, hC]; ring
  have hfin : G2 (Ehi+(beta+1)*t)+K < g1+m*(beta*t) := Nat.lt_of_mul_lt_mul_left hsum
  exact lt_of_lt_of_le hfin htan

end ProximityPrize.SubmissionLower.RelativeBounded6814
end MergedPart9
section MergedPart10
namespace ProximityPrize.SubmissionLower.AsymmetricChainPolynomial80899
open scoped BigOperators
open RCN238 RCN223 RCN260 RCN313 RCN294 BoundaryTailChainHelper AsymmetricHelper
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

def stage (y z d j : ℕ) : UnequalParameters :=
  ⟨262144,131071,181245,y,d-j,z,y,d,z⟩

def kTerm (y z : ℕ) : ℕ :=
  131073 * (z + y + 524284*y*z) + 50174*80900*y
def mTerm (y z : ℕ) : ℕ := 131073*131071*y*z

theorem stageNumerator (y z d j : ℕ) (hj : j ≤ d) :
    leftRegularNumerator (stage y z d j) =
      (2*d-j)*kTerm y z + (2*(d-j)-1)*2*mTerm y z := by
  simp only [stage, leftRegularNumerator, UnequalParameters.gap,
    UnequalParameters.errors, UnequalParameters.leftAgreement,
    UnequalParameters.mixedCost, dot]
  norm_num only
  have hsub : (d-j)+d = 2*d-j := by omega
  dsimp [kTerm, mTerm]
  calc
    _ = ((d-j)+d) * (131073*(z+y+524284*y*z)+50174*80900*y) +
        (2*(d-j)-1)*2*(131073*131071*y*z) := by ring
    _ = _ := by rw [hsub]

def numerator (y z d : ℕ) : ℕ :=
  (d-1)*(3*d*kTerm y z + 4*mTerm y z*(d-1)) + 2*50174*9000000000000

def constant (y d : ℕ) : ℕ :=
  (d-1)*3*d*(131073+50174*80900)*y + 2*50174*9000000000000

private theorem le_roundUp_mul_MovingFiberCountingArithmetic6815 (a b : ℕ) (hb : 0 < b) : a ≤ (a/b+1)*b := by
  have hm := Nat.mod_lt a hb
  have he := Nat.mod_add_div a b
  nlinarith

end ProximityPrize.SubmissionLower.AsymmetricChainPolynomial80899
end MergedPart10
section MergedPart11
namespace ProximityPrize.SubmissionLower.FoldChainPolynomial6815
open scoped BigOperators
open RCN238 RCN223 RCN260 RCN313 RCN294 BoundaryTailChainHelper AsymmetricHelper AsymmetricChainPolynomial80899
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem stageDot (y z d : ℕ) (hd : 1 ≤ d) :
    dot ⟨y, d-1, z⟩ (stage y z d 1).mixedCost = y*z*(6*d-4) := by
  obtain ⟨e, rfl⟩ : ∃ e, d = e+1 := ⟨d-1, by omega⟩
  simp only [stage, dot, UnequalParameters.mixedCost, Nat.add_sub_cancel]
  rw [show 6*(e+1)-4 = 6*e+2 by omega]
  ring

def foldNumerator (y z d : ℕ) : ℕ :=
  leftRegularNumerator (stage y z d 1) + 50174*(y*z*(6*d-4)) + 50174*9000000000000

theorem foldNumerator_int (y z d : ℕ) (hd : 2 ≤ d) :
    (foldNumerator y z d : ℤ) =
      (2*(kTerm y z : ℤ)+4*(mTerm y z : ℤ)+6*50174*(y : ℤ)*z)*d +
        (50174*9000000000000-(kTerm y z : ℤ)-6*(mTerm y z : ℤ)-4*50174*(y : ℤ)*z) := by
  unfold foldNumerator
  rw [stageNumerator y z d 1 (by omega)]
  have e1 : ((2*d-1 : ℕ) : ℤ) = 2*(d : ℤ)-1 := by omega
  have e2 : ((2*(d-1)-1 : ℕ) : ℤ) = 2*(d : ℤ)-3 := by omega
  have e3 : ((6*d-4 : ℕ) : ℤ) = 6*(d : ℤ)-4 := by omega
  push_cast [e1, e2, e3]
  ring

theorem foldNumerator_between (y z d r u : ℕ) (hd : 2 ≤ d) (hdr : d ≤ r)
    (h2 : foldNumerator y z 2 ≤ 2*50174*u) (hr : foldNumerator y z r ≤ r*50174*u) :
    foldNumerator y z d ≤ d*50174*u := by
  by_cases hr2 : r = 2
  · have hd2 : d = 2 := by omega
    subst hd2
    exact h2
  have hk2 := foldNumerator_int y z 2 le_rfl
  have hkr := foldNumerator_int y z r (by omega)
  have hkd := foldNumerator_int y z d hd
  have h2' : (foldNumerator y z 2 : ℤ) ≤ 2*50174*(u : ℤ) := by exact_mod_cast h2
  have hr' : (foldNumerator y z r : ℤ) ≤ (r : ℤ)*50174*(u : ℤ) := by exact_mod_cast hr
  have hid : ((r : ℤ)-2)*((foldNumerator y z d : ℤ)-(d : ℤ)*50174*u) =
      ((r : ℤ)-d)*((foldNumerator y z 2 : ℤ)-2*50174*u) +
        ((d : ℤ)-2)*((foldNumerator y z r : ℤ)-(r : ℤ)*50174*u) := by
    rw [hk2, hkr, hkd]
    push_cast
    ring
  have hA := mul_nonpos_of_nonneg_of_nonpos (show (0 : ℤ) ≤ (r : ℤ)-d by omega)
    (show (foldNumerator y z 2 : ℤ)-2*50174*u ≤ 0 by linarith)
  have hB := mul_nonpos_of_nonneg_of_nonpos (show (0 : ℤ) ≤ (d : ℤ)-2 by omega)
    (show (foldNumerator y z r : ℤ)-(r : ℤ)*50174*u ≤ 0 by linarith)
  have hprod : ((r : ℤ)-2)*((foldNumerator y z d : ℤ)-(d : ℤ)*50174*u) ≤ 0 := by
    rw [hid]
    linarith
  have hpos : (0 : ℤ) < (r : ℤ)-2 := by omega
  have hle : (foldNumerator y z d : ℤ)-(d : ℤ)*50174*u ≤ 0 := by
    by_contra hc
    have := mul_pos hpos (lt_of_not_ge hc)
    linarith
  have hfin : (foldNumerator y z d : ℤ) ≤ (d : ℤ)*50174*u := by linarith
  exact_mod_cast hfin

def foldZCoeff (y d : ℕ) : ℕ :=
  (2*d-1)*131073*(1+524284*y) + (2*d-3)*2*131073*131071*y + 50174*y*(6*d-4)
def foldConstant (y d : ℕ) : ℕ :=
  (2*d-1)*(131073+50174*80900)*y + 50174*9000000000000

theorem foldNumerator_linear (y z d : ℕ) (hd : 1 ≤ d) :
    foldNumerator y z d = foldZCoeff y d*z + foldConstant y d := by
  unfold foldNumerator
  rw [stageNumerator y z d 1 hd, show 2*(d-1)-1 = 2*d-3 by omega]
  unfold kTerm mTerm foldZCoeff foldConstant
  ring

def foldSlope (y d : ℕ) : ℕ := foldZCoeff y d / (50174*d) + 1
def foldConst (y d : ℕ) : ℕ := foldConstant y d / (50174*d) + 1
def foldPiece (y z d : ℕ) : ℕ := foldSlope y d*z + foldConst y d

def foldUnit (y z r : ℕ) : ℕ :=
  if r < 2 then 9000000000000 else
    max 9000000000000 (max (foldPiece y z 2) (foldPiece y z r))

private theorem le_roundUp_mul_FoldChainArithmetic6815 (a b : ℕ) (hb : 0 < b) : a ≤ (a/b+1)*b := by
  have hm := Nat.mod_lt a hb
  have he := Nat.mod_add_div a b
  nlinarith

theorem foldPiece_end (y z d : ℕ) (hd : 1 ≤ d) :
    foldNumerator y z d ≤ d*50174*foldPiece y z d := by
  have hb : 0 < 50174*d := by omega
  have ha := le_roundUp_mul_FoldChainArithmetic6815 (foldZCoeff y d) (50174*d) hb
  have hc := le_roundUp_mul_FoldChainArithmetic6815 (foldConstant y d) (50174*d) hb
  have ham := Nat.mul_le_mul_right z ha
  rw [foldNumerator_linear y z d hd]
  unfold foldPiece foldSlope foldConst
  nlinarith

theorem tail_le_foldUnit (y z r : ℕ) : 9000000000000 ≤ foldUnit y z r := by
  unfold foldUnit
  split_ifs
  · exact le_rfl
  · exact le_max_left _ _

theorem foldNumerator_le_unit (y z d r : ℕ) (hd : 2 ≤ d) (hdr : d ≤ r) :
    foldNumerator y z d ≤ d*50174*foldUnit y z r := by
  have hr : ¬ r < 2 := by omega
  have h2 : foldPiece y z 2 ≤ foldUnit y z r := by
    unfold foldUnit
    rw [if_neg hr]
    exact (le_max_left _ _).trans (le_max_right _ _)
  have hrr : foldPiece y z r ≤ foldUnit y z r := by
    unfold foldUnit
    rw [if_neg hr]
    exact (le_max_right _ _).trans (le_max_right _ _)
  apply foldNumerator_between y z d r (foldUnit y z r) hd hdr
  · exact (foldPiece_end y z 2 (by decide)).trans (Nat.mul_le_mul_left _ h2)
  · exact (foldPiece_end y z r (by omega)).trans (Nat.mul_le_mul_left _ hrr)

end ProximityPrize.SubmissionLower.FoldChainPolynomial6815
end MergedPart11
section MergedPart12
namespace ProximityPrize.SubmissionLower.PairCell6815
open RCN260 RCN294 AsymmetricHelper
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

def parameters (r y t : ℕ) : UnequalParameters :=
  ⟨262144,131071,181245,229-y,50-r,15421-t,348-y,78-r,11193-t⟩

def cap (r y t : ℕ) : ℕ := leftRegularCountCap (parameters r y t)

def constant (r y : ℕ) : ℕ := leftRegularNumerator (parameters r y 0)

def slope (r y : ℕ) : ℕ :=
  131073*((1+2*131071*(229-y))*((50-r)+(78-r)) +
    131071*(2*(50-r)-1)*((229-y)+(348-y)) +
    2*131071*((229-y)*(78-r)+(50-r)*(348-y)))

theorem numerator_affine (r y t : ℕ) (ht : t ≤ 11193) :
    leftRegularNumerator (parameters r y t) + slope r y * t = constant r y := by
  have ht' : t ≤ 15421 := by omega
  simp only [constant, slope, parameters, leftRegularNumerator, UnequalParameters.errors,
    UnequalParameters.gap, UnequalParameters.leftAgreement, UnequalParameters.mixedCost,
    dot, Nat.sub_zero]
  zify [ht, ht']
  ring

def line (r y t : ℕ) : ℤ :=
  ((constant r y / 50174 : ℕ) : ℤ) - ((slope r y / 50174 : ℕ) : ℤ) * (t : ℤ)

theorem cap_le_line (r y t : ℕ) (ht : t ≤ 11193) : (cap r y t : ℤ) ≤ line r y t := by
  have he := numerator_affine r y t ht
  have h1 := Nat.div_mul_le_self (leftRegularNumerator (parameters r y t)) 50174
  have h2 := Nat.div_add_mod (constant r y) 50174
  have h3 := Nat.mod_lt (constant r y) (show 0 < 50174 by norm_num)
  have h4 := Nat.mul_le_mul_right t (Nat.div_mul_le_self (slope r y) 50174)
  have hn : cap r y t + slope r y / 50174 * t ≤ constant r y / 50174 := by
    have hc : cap r y t = leftRegularNumerator (parameters r y t) / 50174 := by
      simp only [cap, leftRegularCountCap, parameters, UnequalParameters.gap]
    have h5 : slope r y / 50174 * 50174 * t = 50174 * (slope r y / 50174 * t) := by ring
    rw [h5] at h4
    rw [hc]
    generalize slope r y / 50174 * t = P at *
    generalize slope r y * t = S at *
    omega
  unfold line
  have hn' := (Nat.cast_le (α := ℤ)).mpr hn
  rw [Nat.cast_add, Nat.cast_mul] at hn'
  linarith

end ProximityPrize.SubmissionLower.PairCell6815
end MergedPart12
