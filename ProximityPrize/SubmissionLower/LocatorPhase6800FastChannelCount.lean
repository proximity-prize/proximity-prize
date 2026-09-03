import ProximityPrize.SubmissionLower.LocatorPhase6800ReceiptCellCore

namespace ProximityPrize.SubmissionLower.ThresholdFastProof

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
      rw [kernelSumRange, kernelSumRange_succ_all]
      simpa [Nat.choose_one_right, Nat.add_comm, Nat.add_left_comm,
        Nat.add_assoc] using (Nat.choose_succ_succ (n + 1) 1).symm

theorem kernelSumRange_succ (U : ℕ) :
    kernelSumRange (fun x => x + 1) (U + 1) = (U + 2).choose 2 := by
  simpa only [Nat.add_assoc] using kernelSumRange_succ_all (U + 1)

theorem kernelSumRange_choose_two_all : ∀ n : ℕ,
    kernelSumRange (fun x => (x + 1).choose 2) n = (n + 1).choose 3
  | 0 => by decide
  | n + 1 => by
      rw [kernelSumRange, kernelSumRange_choose_two_all]
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

/-! ## Constant-time executable form -/

theorem choose_three_right (n : ℕ) :
    n.choose 3 = n * (n - 1) * (n - 2) / 6 := by
  rw [Nat.choose_eq_descFactorial_div_factorial]
  simp [Nat.descFactorial, Nat.factorial]
  congr 1
  ring

def evalChooseTwo (n : ℕ) : ℕ := n * (n - 1) / 2
def evalChooseThree (n : ℕ) : ℕ := n * (n - 1) * (n - 2) / 6

/-- A constant-time executable version of `channelCount`. -/
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

open LocatorArbitraryPowerAvoidance LocatorPhase6800Oracle
open RCN095 LocatorFactorAggregate LocatorPhase6800ReceiptCellCore

/-- Executable power-band budget with the expensive range sum replaced by
the proved constant-time channel-count formula. -/
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
  evalPowerBandBudget 50322 (total p) (middle p) p.all
    (s.totalCap - total p) (s.middleCap - middle p)
    (s.slopeCap - p.all) (s.fuel p)

theorem evalBand_eq (s : SourceNumbers) (p : FlagDegree) :
    evalBand s p = s.band p := by
  unfold evalBand SourceNumbers.band
  exact evalPowerBandBudget_eq _ _ _ _ _ _ _ _

def FastRouteable (s : SourceNumbers) (p : FlagDegree) : Prop :=
  1 ≤ p.all ∧ total p ≤ s.totalCap ∧ middle p ≤ s.middleCap ∧
    p.all ≤ s.slopeCap ∧ evalBand s p < s.gap

instance (s : SourceNumbers) (p : FlagDegree) :
    Decidable (FastRouteable s p) := by
  unfold FastRouteable
  infer_instance

theorem fastRouteable_iff (s : SourceNumbers) (p : FlagDegree) :
    FastRouteable s p ↔ s.Routeable p := by
  unfold FastRouteable SourceNumbers.Routeable
  rw [evalBand_eq]

def FastSourceThresholdSufficient
    (s : SourceNumbers) (r v threshold : ℕ) : Prop :=
  5964 - (r + v) < threshold ∨ FastRouteable s (rawFlag r v threshold)

instance (s : SourceNumbers) (r v threshold : ℕ) :
    Decidable (FastSourceThresholdSufficient s r v threshold) := by
  unfold FastSourceThresholdSufficient
  infer_instance

def FastThresholdSufficient (q : ThresholdReceipt) : Prop :=
  1 ≤ q.r ∧ q.r ≤ 28 ∧ q.r + q.v ≤ 127 ∧
    FastSourceThresholdSufficient sourceR1200 q.r q.v q.r1200 ∧
    FastSourceThresholdSufficient LocatorPhase6800Oracle.sourceC
      q.r q.v q.sourceC ∧
    FastSourceThresholdSufficient sourceSplit500 q.r q.v q.split500 ∧
    FastSourceThresholdSufficient sourceSplit390 q.r q.v q.split390

instance (q : ThresholdReceipt) : Decidable (FastThresholdSufficient q) := by
  unfold FastThresholdSufficient
  infer_instance

theorem fastSourceThresholdSufficient_sound
    (s : SourceNumbers) (r v threshold : ℕ) :
    FastSourceThresholdSufficient s r v threshold →
      SourceThresholdSufficient s r v threshold := by
  intro h
  rcases h with h | h
  · exact Or.inl h
  · exact Or.inr ((fastRouteable_iff s _).mp h)

theorem fastThresholdSufficient_sound (q : ThresholdReceipt) :
    FastThresholdSufficient q → ThresholdSufficient q := by
  intro h
  rcases h with ⟨hr1, hr28, hrv, hR, hC, hF, hS⟩
  exact ⟨hr1, hr28, hrv,
    fastSourceThresholdSufficient_sound _ _ _ _ hR,
    fastSourceThresholdSufficient_sound _ _ _ _ hC,
    fastSourceThresholdSufficient_sound _ _ _ _ hF,
    fastSourceThresholdSufficient_sound _ _ _ _ hS⟩

/-! ## Whole-row executable interfaces -/

def FastThresholdAtOf
    (row : ℕ → ThresholdReceipt) (R V : ℕ) : Prop :=
  let q := row V
  q.r = R ∧ q.v = V ∧ FastThresholdSufficient q

instance (row : ℕ → ThresholdReceipt) (R V : ℕ) :
    Decidable (FastThresholdAtOf row R V) := by
  unfold FastThresholdAtOf
  infer_instance

theorem fastThresholdAtOf_sound
    (row : ℕ → ThresholdReceipt) (R V : ℕ) :
    FastThresholdAtOf row R V → ThresholdAtOf row R V := by
  intro h
  rcases h with ⟨hr, hv, hs⟩
  exact ⟨hr, hv, fastThresholdSufficient_sound _ hs⟩

def FastThresholdRIndexedOf
    (row : ℕ → ThresholdReceipt) (R count : ℕ) : Prop :=
  ∀ V ∈ List.range count, FastThresholdAtOf row R V

instance (row : ℕ → ThresholdReceipt) (R count : ℕ) :
    Decidable (FastThresholdRIndexedOf row R count) := by
  unfold FastThresholdRIndexedOf
  infer_instance

def PrefixCoreRIndexedOf
    (row nextRow : ℕ → PrefixReceipt) (R count : ℕ) : Prop :=
  ∀ V ∈ List.range count, PrefixCoreAtOf row nextRow R V

instance (row nextRow : ℕ → PrefixReceipt) (R count : ℕ) :
    Decidable (PrefixCoreRIndexedOf row nextRow R count) := by
  unfold PrefixCoreRIndexedOf
  infer_instance

end ProximityPrize.SubmissionLower.ThresholdFastProof
