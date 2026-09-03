import ProximityPrize.SubmissionLower.LocatorPhase6802Oracle

/-!
# Soundness utilities for the compact 6802 phase receipt

These lemmas are deliberately separate from the generated receipt data.  The
first records the correlated (rather than independent-maxima) initial-A
ledger.  The remaining lemmas justify interpreting a checked threshold row as
an exact routeability cutoff in the raw total coordinate.
-/

namespace ProximityPrize.SubmissionLower.LocatorPhase6802Audit

open scoped BigOperators
open RCN095 LocatorFactorAggregate LocatorArbitraryPowerAvoidance
open LocatorPhase6802Oracle

set_option autoImplicit false
set_option maxRecDepth 100000

/-- The initial-A ledger has to retain the common aggregate `p`: the maximum
phase cost and maximum complementary A charge cannot be taken independently. -/
theorem initialA_sum_le_certifiedJoint_correlated
    (oracle : CheckedPhaseOracle)
    (phaseSum helperSum : ℕ) (p : FlagDegree)
    (hslope : p.all ≤ 29) (hmiddle : middle p ≤ 132)
    (htotal : total p ≤ 6403)
    (hphase : phaseSum ≤ oracle.narrowCap p)
    (hhelper : helperSum ≤ initialAComplement p) :
    phaseSum + helperSum ≤ certifiedJointMaximum := by
  exact (Nat.add_le_add hphase hhelper).trans
    (oracle.joint_le p hslope hmiddle htotal)

/-- Taking one more high-band projection only adds a nonnegative summand. -/
theorem powerBandBudget_le_succ
    (delta dT dY dS T YS S k : ℕ) :
    powerBandBudget delta dT dY dS T YS S k ≤
      powerBandBudget delta dT dY dS T YS S (k + 1) := by
  induction k generalizing T YS S with
  | zero =>
      simp only [powerBandBudget, Nat.zero_add]
      exact Nat.zero_le _
  | succ k ih =>
      simp only [powerBandBudget]
      exact Nat.add_le_add_left
        (ih (T := T - dT) (YS := YS - dY) (S := S - dS)) _

/-- The cumulative high-band cost is monotone in the number of projections. -/
theorem powerBandBudget_mono_fuel
    (delta dT dY dS T YS S : ℕ) {k₁ k₂ : ℕ} (hk : k₁ ≤ k₂) :
    powerBandBudget delta dT dY dS T YS S k₁ ≤
      powerBandBudget delta dT dY dS T YS S k₂ := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hk
  induction d with
  | zero => simp
  | succ d ih =>
      calc
        powerBandBudget delta dT dY dS T YS S k₁ ≤
            powerBandBudget delta dT dY dS T YS S (k₁ + d) :=
          ih (Nat.le_add_right _ _)
        _ ≤ powerBandBudget delta dT dY dS T YS S ((k₁ + d) + 1) :=
          powerBandBudget_le_succ delta dT dY dS T YS S (k₁ + d)
        _ = powerBandBudget delta dT dY dS T YS S (k₁ + d.succ) := by
          congr 1

/-- For fixed raw slope and middle coordinates, increasing `z` can only make
the source route easier: the residual total box and the fuel both decrease. -/
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
      powerBandBudget 50303 (r + v + z₂) (r + v) r
          (s.totalCap - (r + v + z₂)) (s.middleCap - (r + v))
          (s.slopeCap - r) (s.fuel (rawFlag r v z₂)) ≤
        powerBandBudget 50303 (r + v + z₁) (r + v) r
          (s.totalCap - (r + v + z₁)) (s.middleCap - (r + v))
          (s.slopeCap - r) (s.fuel (rawFlag r v z₂)) := by
    exact powerBandBudget_mono 50303
      (r + v + z₂) (r + v) r
      (s.totalCap - (r + v + z₂)) (s.middleCap - (r + v))
      (s.slopeCap - r)
      (r + v + z₁) (r + v) r
      (s.totalCap - (r + v + z₁)) (s.middleCap - (r + v))
      (s.slopeCap - r) (s.fuel (rawFlag r v z₂))
      hbox (le_refl _) (le_refl _) htotal (le_refl _) (le_refl _)
  have hmoreFuel :
      powerBandBudget 50303 (r + v + z₁) (r + v) r
          (s.totalCap - (r + v + z₁)) (s.middleCap - (r + v))
          (s.slopeCap - r) (s.fuel (rawFlag r v z₂)) ≤
        powerBandBudget 50303 (r + v + z₁) (r + v) r
          (s.totalCap - (r + v + z₁)) (s.middleCap - (r + v))
          (s.slopeCap - r) (s.fuel (rawFlag r v z₁)) :=
    powerBandBudget_mono_fuel 50303 (r + v + z₁) (r + v) r
      (s.totalCap - (r + v + z₁)) (s.middleCap - (r + v))
      (s.slopeCap - r) hfuel
  refine ⟨hr, ?_, ?_, ?_, ?_⟩
  · simpa only [rawFlag_total] using hcap
  · simpa only [rawFlag_middle] using hy
  · simpa only [rawFlag_all] using hs
  · unfold SourceNumbers.band at hband ⊢
    simp only [rawFlag_total, rawFlag_middle, rawFlag_all] at hband ⊢
    exact (hsameFuel.trans hmoreFuel).trans_lt hband

/-- A valid threshold boundary is the exact routeability cutoff throughout
the benchmark raw-total interval. -/
theorem routeable_raw_iff_threshold
    (s : SourceNumbers) {r v threshold z : ℕ}
    (hsourceCap : 6403 ≤ s.totalCap)
    (hrv : r + v ≤ 6403) (hz : z ≤ 6403 - (r + v))
    (hboundary : thresholdBoundary s r v threshold) :
    s.Routeable (rawFlag r v z) ↔ threshold ≤ z := by
  unfold thresholdBoundary at hboundary
  by_cases hzero : threshold = 0
  · rw [if_pos hzero] at hboundary
    constructor
    · intro _
      omega
    · intro _
      apply routeable_raw_mono_z s (z₁ := 0) (z₂ := z)
      · omega
      · omega
      · exact hboundary
  · rw [if_neg hzero] at hboundary
    by_cases hin : threshold ≤ 6403 - (r + v)
    · rw [if_pos hin] at hboundary
      constructor
      · intro hroute
        by_contra hnot
        have hzprev : z ≤ threshold - 1 := by omega
        have hroutePrev := routeable_raw_mono_z s hzprev (by omega) hroute
        exact hboundary.1 hroutePrev
      · intro hthreshold
        exact routeable_raw_mono_z s hthreshold (by omega) hboundary.2
    · rw [if_neg hin] at hboundary
      constructor
      · intro hroute
        have hrouteMax := routeable_raw_mono_z s hz (by omega) hroute
        exact False.elim (hboundary.2 hrouteMax)
      · intro hthreshold
        omega

/-! ## Noncircular semantics of a prefix receipt -/

theorem sumFlag_rawBelow_of_subset
    {ι : Type} [DecidableEq ι] (flag : ι → FlagDegree)
    {A U : Finset ι} (hUA : U ⊆ A) :
    RawBelow (sumFlag U flag) (sumFlag A flag) := by
  refine ⟨?_, ?_, ?_⟩ <;>
    exact Finset.sum_le_sum_of_subset_of_nonneg hUA
      (fun _ _ _ ↦ Nat.zero_le _)

/-- A proper subfamily has strictly smaller raw slope when every factor has
positive slope.  This is the well-founded coordinate behind `afterR = r-1`. -/
theorem sumFlag_all_lt_of_ssubset
    {ι : Type} [DecidableEq ι] (flag : ι → FlagDegree)
    {A U : Finset ι} (hUA : U ⊂ A)
    (hpositive : ∀ i ∈ A, 1 ≤ (flag i).all) :
    (sumFlag U flag).all < (sumFlag A flag).all := by
  have hdiff : (A \ U).Nonempty := by
    exact Finset.sdiff_nonempty.mpr (fun hAU ↦ hUA.ne (Finset.Subset.antisymm hUA.subset hAU))
  obtain ⟨i, hi⟩ := hdiff
  have hiA : i ∈ A := (Finset.mem_sdiff.mp hi).1
  have hiOne : 1 ≤ (flag i).all := hpositive i hiA
  have hiSum : (flag i).all ≤ ∑ j ∈ A \ U, (flag j).all := by
    exact Finset.single_le_sum
      (f := fun j ↦ (flag j).all) (fun _ _ ↦ Nat.zero_le _) hi
  have hsplit := Finset.sum_sdiff hUA.subset (f := fun j ↦ (flag j).all)
  simp only [sumFlag_all] at *
  omega

/-- Additivity of every numerical phase potential on a finite family. -/
theorem sum_potential_eval
    {ι : Type} [DecidableEq ι] (s : Finset ι)
    (flag : ι → FlagDegree) (q : Potential) :
    (∑ i ∈ s, q.eval (flag i)) = q.eval (sumFlag s flag) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [sumFlag, Potential.eval, total, middle]
  | @insert i s hi ih =>
      simp only [Finset.sum_insert hi, ih]
      simp [sumFlag, Potential.eval, total, middle, hi]
      ring

/-- Semantic content of one cumulative prefix table.  `terminal` checks only
actual nonrouteable states.  `monotone` records the cumulative max closure in
raw `r`, `v`, and `z`; neither field assumes the desired phase bound. -/
structure PrefixTableSound
    (previous : FlagDegree → ℕ) (q : Potential)
    (routeable : FlagDegree → Prop) (pref : FlagDegree → ℕ) : Prop where
  terminal : ∀ p, ¬ routeable p →
    previous p ≤ q.eval p + pref p
  monotone : ∀ {p₁ p₂}, RawBelow p₁ p₂ → pref p₁ ≤ pref p₂

/-- A parent of raw slope `r` queries the prefix after completing slope
`r-1`.  The subtraction is harmless at zero; routed nonempty products have
positive slope. -/
def parentDefect (pref : FlagDegree → ℕ) (parent : FlagDegree) : ℕ :=
  pref (rawFlag (parent.all - 1) parent.yz parent.zOnly)

/-- The value after adjoining one source phase. -/
def applyPhase (previous : FlagDegree → ℕ) (q : Potential)
    (routeable : FlagDegree → Prop) [DecidablePred routeable]
    (pref : FlagDegree → ℕ)
    (p : FlagDegree) : ℕ :=
  if routeable p then
    min (previous p) (q.eval p + parentDefect pref p)
  else previous p

/-- Reapplying an identical source phase is pointwise idempotent. -/
theorem applyPhase_self_at
    (previous : FlagDegree → ℕ) (q : Potential)
    (routeable : FlagDegree → Prop) [DecidablePred routeable]
    (pref : FlagDegree → ℕ) (p : FlagDegree) :
    applyPhase (applyPhase previous q routeable pref) q routeable pref p =
      applyPhase previous q routeable pref p := by
  unfold applyPhase
  by_cases hroute : routeable p
  · simp only [if_pos hroute]
    exact min_eq_left (min_le_right _ _)
  · simp only [if_neg hroute]

theorem applyPhase_self
    (previous : FlagDegree → ℕ) (q : Potential)
    (routeable : FlagDegree → Prop) [DecidablePred routeable]
    (pref : FlagDegree → ℕ) :
    applyPhase (applyPhase previous q routeable pref) q routeable pref =
      applyPhase previous q routeable pref := by
  funext p
  exact applyPhase_self_at previous q routeable pref p

/-- A checked prefix remains sound when its identical phase is applied again. -/
theorem PrefixTableSound.selfApply
    (previous pref : FlagDegree → ℕ) (q : Potential)
    (routeable : FlagDegree → Prop) [DecidablePred routeable]
    (hrows : PrefixTableSound previous q routeable pref) :
    PrefixTableSound (applyPhase previous q routeable pref)
      q routeable pref := by
  refine ⟨?_, hrows.monotone⟩
  intro p hterminal
  simpa only [applyPhase, if_neg hterminal] using
    hrows.terminal p hterminal

/-- A cumulative prefix row bounds every nonrouteable strict child of its
parent.  This is the exact semantic fact needed by the algebraic batch split. -/
theorem terminal_le_parent_charge
    {previous pref : FlagDegree → ℕ} {q : Potential}
    {routeable : FlagDegree → Prop}
    (hrows : PrefixTableSound previous q routeable pref)
    {child parent : FlagDegree} (hbelow : RawBelow child parent)
    (hslope : child.all < parent.all) (hterminal : ¬ routeable child) :
    previous child ≤ q.eval child + parentDefect pref parent := by
  have hpred : RawBelow child
      (rawFlag (parent.all - 1) parent.yz parent.zOnly) := by
    rcases hbelow with ⟨hr, hv, hz⟩
    refine ⟨?_, ?_, ?_⟩
    · simpa only [rawFlag_all]
      using (show child.all ≤ parent.all - 1 by omega)
    · simpa only [rawFlag] using hv
    · simpa only [rawFlag] using hz
  simpa only [parentDefect] using (hrows.terminal child hterminal).trans
    (Nat.add_le_add_left (hrows.monotone hpred) _)

/-- Soundness of one checked numerical phase.  The proof deliberately keeps
the previous bound state-local.  When the current aggregate routes, repeated
strict algebraic splits terminate at a nonrouteable subfamily covered by the
prefix table; exited factors are charged by the additive source potential. -/
theorem sum_count_le_applyPhase
    {ι : Type} [DecidableEq ι]
    (flag : ι → FlagDegree) (count : ι → ℕ)
    (previous : FlagDegree → ℕ) (q : Potential)
    (routeable : FlagDegree → Prop) [DecidablePred routeable]
    (pref : FlagDegree → ℕ)
    (ambient : Finset ι)
    (hpositive : ∀ i ∈ ambient, 1 ≤ (flag i).all)
    (hprevious : ∀ B, B ⊆ ambient →
      (∑ i ∈ B, count i) ≤ previous (sumFlag B flag))
    (hrows : PrefixTableSound previous q routeable pref)
    (hroute : ∀ B, B ⊆ ambient → routeable (sumFlag B flag) →
      ∃ U, U ⊂ B ∧
        (∑ i ∈ B \ U, count i) ≤
          ∑ i ∈ B \ U, q.eval (flag i)) :
    (∑ i ∈ ambient, count i) ≤
      applyPhase previous q routeable pref (sumFlag ambient flag) := by
  classical
  by_cases hr : routeable (sumFlag ambient flag)
  · rw [applyPhase, if_pos hr]
    apply le_min
    · exact hprevious ambient (fun _ hi ↦ hi)
    · have hcharged :=
        LocatorBatchProductRoute.sum_count_le_charge_add_defect_of_strict_routes
          count (fun i ↦ q.eval (flag i))
          (fun B ↦ routeable (sumFlag B flag)) ambient
          (parentDefect pref (sumFlag ambient flag))
          (fun B hB hn ↦ by
            have hprev := hprevious B hB
            by_cases hEq : B = ambient
            · subst B
              exact False.elim (hn hr)
            · have hproper : B ⊂ ambient :=
                (_root_.ssubset_iff_subset_ne).mpr ⟨hB, hEq⟩
              have hraw := sumFlag_rawBelow_of_subset flag hB
              have hslope := sumFlag_all_lt_of_ssubset flag hproper hpositive
              rw [sum_potential_eval B flag q]
              exact hprev.trans
                (terminal_le_parent_charge hrows hraw hslope hn))
          hroute
      rw [sum_potential_eval ambient flag q] at hcharged
      exact hcharged
  · rw [applyPhase, if_neg hr]
    exact hprevious ambient (fun _ hi ↦ hi)

/-- A threshold function is semantically checked by boundary receipts at
every raw `(r,v)` row. -/
def ThresholdTableSound (s : SourceNumbers)
    (threshold : ℕ → ℕ → ℕ) : Prop :=
  ∀ r v, 1 ≤ r → r + v ≤ 132 →
    thresholdBoundary s r v (threshold r v)

theorem routeable_iff_of_thresholdTableSound
    (s : SourceNumbers) (threshold : ℕ → ℕ → ℕ)
    (hsourceCap : 6403 ≤ s.totalCap)
    (htable : ThresholdTableSound s threshold)
    (p : FlagDegree) (hr : 1 ≤ p.all)
    (hy : middle p ≤ 132) (ht : total p ≤ 6403) :
    s.Routeable p ↔ threshold p.all p.yz ≤ p.zOnly := by
  have hry : p.all + p.yz ≤ 132 := by
    simpa only [middle, Nat.add_comm] using hy
  have hrz : p.zOnly ≤ 6403 - (p.all + p.yz) := by
    simp only [total] at ht
    omega
  have hryWide : p.all + p.yz ≤ 6403 := hry.trans (by decide)
  have h := routeable_raw_iff_threshold s hsourceCap
    (r := p.all) (v := p.yz) (z := p.zOnly)
    (hrv := hryWide) (hz := hrz)
    (hboundary := htable p.all p.yz hr hry)
  simpa only [rawFlag] using h


end ProximityPrize.SubmissionLower.LocatorPhase6802Audit
