import ProximityPrize.SubmissionLower.LocatorPhase6802Checked

namespace ProximityPrize.SubmissionLower.LocatorBatchPhase6802

open ProximityPrize.Benchmark
open scoped BigOperators
open RCN071 RCN081 RCN095 RCN100 RCN101 RCN119 RCN130 RCN140 RCN156
  RCN180 RCN234 RCN238 RCN260 RCN266
open LocatorFactorAggregate LocatorArbitraryPowerAvoidance
  LocatorBatchProductRoute LocatorBatchPowerRoute6802
  LocatorGenericHelperFactorSwitch6802 LocatorPhase6802Oracle

noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

abbrev K := IRSProfile.Field
abbrev I := IRSProfile.Index
abbrev P4 := MvPolynomial (Fin 4) K

local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I

/-- Additive flag of a finite batch of regular factors. -/
def regularAggregateFlag (H : P4) (A : Finset (RegularIndex H)) : FlagDegree :=
  sumFlag A (regularCumulativeFlag H)

private theorem regularProduct_weight_eq_sum
    (weights : Fin 4 → ℕ) (H : P4) (A : Finset (RegularIndex H)) :
    wt weights (regularProduct H A) = ∑ F ∈ A, wt weights F.1 := by
  have h := weightedTotalDegree_prod_eq weights A
    (fun F : RegularIndex H => F.1)
    (fun F _hF => regularFactor_ne_zero H F)
  simpa only [regularProduct, wt] using h

theorem regularAggregateFlag_all (H : P4) (A : Finset (RegularIndex H)) :
    (regularAggregateFlag H A).all =
      wt residualSWeights (regularProduct H A) := by
  rw [regularAggregateFlag, sumFlag_all]
  calc
    (∑ F ∈ A, (regularCumulativeFlag H F).all) =
        ∑ F ∈ A, wt residualSWeights F.1 := by
      apply Finset.sum_congr rfl
      intro F _hF
      exact (originalCumulativeFlag_cumulative F.1).1
    _ = wt residualSWeights (regularProduct H A) :=
      (regularProduct_weight_eq_sum residualSWeights H A).symm

theorem regularAggregateFlag_middle (H : P4)
    (A : Finset (RegularIndex H)) :
    middle (regularAggregateFlag H A) =
      wt residualYSWeights (regularProduct H A) := by
  rw [regularAggregateFlag, sumFlag_middle]
  calc
    (∑ F ∈ A, middle (regularCumulativeFlag H F)) =
        ∑ F ∈ A, wt residualYSWeights F.1 := by
      apply Finset.sum_congr rfl
      intro F _hF
      exact (originalCumulativeFlag_cumulative F.1).2.1
    _ = wt residualYSWeights (regularProduct H A) :=
      (regularProduct_weight_eq_sum residualYSWeights H A).symm

theorem regularAggregateFlag_total (H : P4)
    (A : Finset (RegularIndex H)) :
    total (regularAggregateFlag H A) =
      wt residualTotalWeights (regularProduct H A) := by
  rw [regularAggregateFlag, sumFlag_total]
  calc
    (∑ F ∈ A, total (regularCumulativeFlag H F)) =
        ∑ F ∈ A, wt residualTotalWeights F.1 := by
      apply Finset.sum_congr rfl
      intro F _hF
      exact (originalCumulativeFlag_cumulative F.1).2.2
    _ = wt residualTotalWeights (regularProduct H A) :=
      (regularProduct_weight_eq_sum residualTotalWeights H A).symm

theorem regularAggregateFlag_mono (H : P4)
    {A B : Finset (RegularIndex H)} (hAB : A ⊆ B) :
    (regularAggregateFlag H A).all ≤ (regularAggregateFlag H B).all ∧
      middle (regularAggregateFlag H A) ≤
        middle (regularAggregateFlag H B) ∧
      total (regularAggregateFlag H A) ≤
        total (regularAggregateFlag H B) := by
  simp only [regularAggregateFlag, sumFlag_all, sumFlag_middle, sumFlag_total]
  exact ⟨Finset.sum_le_sum_of_subset hAB,
    Finset.sum_le_sum_of_subset hAB, Finset.sum_le_sum_of_subset hAB⟩

theorem regularAggregateFlag_all_lt_of_ssubset (H : P4)
    {A B : Finset (RegularIndex H)} (hAB : A ⊂ B) :
    (regularAggregateFlag H A).all < (regularAggregateFlag H B).all := by
  have hnBA : ¬ B ⊆ A := by
    intro hBA
    exact hAB.ne (Finset.Subset.antisymm hAB.subset hBA)
  simp only [Finset.subset_iff, not_forall, _root_.not_imp] at hnBA
  obtain ⟨F, hFB, hFA⟩ := hnBA
  simp only [regularAggregateFlag, sumFlag_all]
  exact Finset.sum_lt_sum_of_subset hAB.subset hFB hFA
    (regularCumulativeFlag_positive H F)
    (fun _ _ _ => Nat.zero_le _)

private theorem sourceFuel_pos (s : SourceNumbers) (p : FlagDegree)
    (hr : 1 ≤ p.all) (ht : total p ≤ s.totalCap)
    (hy : middle p ≤ s.middleCap) (hs : p.all ≤ s.slopeCap) :
    1 ≤ s.fuel p := by
  have hmiddle : 1 ≤ middle p := hr.trans (all_le_middle p)
  have htotal : 1 ≤ total p := hmiddle.trans (middle_le_total p)
  unfold SourceNumbers.fuel
  apply le_min
  · exact (Nat.le_div_iff_mul_le htotal).mpr (by simpa using ht)
  · apply le_min
    · exact (Nat.le_div_iff_mul_le hmiddle).mpr (by simpa using hy)
    · exact (Nat.le_div_iff_mul_le hr).mpr (by simpa using hs)

private theorem sourceFuel_feasible (s : SourceNumbers) (p : FlagDegree)
    (hr : 1 ≤ p.all) :
    s.fuel p * total p ≤ s.totalCap ∧
      s.fuel p * middle p ≤ s.middleCap ∧
      s.fuel p * p.all ≤ s.slopeCap := by
  have hmiddle : 1 ≤ middle p := hr.trans (all_le_middle p)
  have htotal : 1 ≤ total p := hmiddle.trans (middle_le_total p)
  unfold SourceNumbers.fuel
  refine ⟨?_, ?_, ?_⟩
  · apply (Nat.le_div_iff_mul_le htotal).mp
    exact min_le_left _ _
  · apply (Nat.le_div_iff_mul_le hmiddle).mp
    exact (min_le_right _ _).trans (min_le_left _ _)
  · apply (Nat.le_div_iff_mul_le hr).mp
    exact (min_le_right _ _).trans (min_le_right _ _)

private theorem div_remainder_lt (a b : ℕ) (hb : 0 < b) :
    a - (a / b) * b < b := by
  have hm := Nat.mod_lt a hb
  have heq := Nat.mod_add_div' a b
  omega

private theorem sourceFuel_terminal (s : SourceNumbers) (p : FlagDegree)
    (hr : 1 ≤ p.all) :
    s.totalCap - s.fuel p * total p < total p ∨
      s.middleCap - s.fuel p * middle p < middle p ∨
      s.slopeCap - s.fuel p * p.all < p.all := by
  have hall : 0 < p.all := by omega
  have hmiddle : 0 < middle p := hall.trans_le (all_le_middle p)
  have htotal : 0 < total p := hmiddle.trans_le (middle_le_total p)
  unfold SourceNumbers.fuel
  by_cases hT : s.totalCap / total p ≤
      min (s.middleCap / middle p) (s.slopeCap / p.all)
  · left
    rw [min_eq_left hT]
    exact div_remainder_lt s.totalCap (total p) htotal
  · rw [min_eq_right (Nat.le_of_not_ge hT)]
    by_cases hY : s.middleCap / middle p ≤ s.slopeCap / p.all
    · right; left
      rw [min_eq_left hY]
      exact div_remainder_lt s.middleCap (middle p) hmiddle
    · right; right
      rw [min_eq_right (Nat.le_of_not_ge hY)]
      exact div_remainder_lt s.slopeCap p.all hr

/-- A numerical route for an aggregate flag supplies the strict algebraic
split required by the phase recursion. -/
theorem routeable_exists_strict_helper_split
    (sound : PhaseSourceSound) (D m : ℕ)
    (hweighted : D = m * 181373)
    (hshape : D + sound.source.slopeCap ≤
      131071 * (sound.source.middleCap + 1))
    (hslopeM : sound.source.slopeCap ≤ m)
    (hmChar : m < 2130706433)
    (u0 u1 : I → K) (H : P4)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hdegree : ∀ gamma ∈ Gamma,
      (selected gamma).natDegree ≤ 131071)
    (hagreement : ∀ gamma ∈ Gamma, 181373 ≤
      ((Finset.univ : Finset I).filter (fun i ↦
        (selected gamma).eval (IRSProfile.domain i) =
          u0 i + gamma * u1 i)).card)
    (hno : NoLargeSelectedPencil selected Gamma 131071 80771)
    (hgap : sound.source.gap ≤ Module.finrank K
      (ConstraintKernel (K := K) D 131071 sound.source.totalCap
        sound.source.slopeCap m IRSProfile.domain u0 u1))
    (A : Finset (RegularIndex H))
    (hroute : sound.source.Routeable (regularAggregateFlag H A))
    (hnarrowS : (regularAggregateFlag H A).all ≤ 29)
    (hnarrowY : middle (regularAggregateFlag H A) ≤ 132)
    (hnarrowT : total (regularAggregateFlag H A) ≤ 6403) :
    ∃ U, U ⊂ A ∧ ∀ F ∈ A \ U,
      (regularSeeds H selected Gamma F).card ≤
        sound.potential.eval (regularCumulativeFlag H F) := by
  classical
  let p := regularAggregateFlag H A
  have hr : 1 ≤ p.all := hroute.1
  have hA : A.Nonempty := by
    by_contra hzero
    have hAe : A = ∅ := Finset.not_nonempty_iff_eq_empty.mp hzero
    subst A
    simp [p, regularAggregateFlag, sumFlag] at hr
  have hfuel : 1 ≤ sound.source.fuel p :=
    sourceFuel_pos sound.source p hr hroute.2.1 hroute.2.2.1
      hroute.2.2.2.1
  have hfeasibleP := sourceFuel_feasible sound.source p hr
  have hterminalP := sourceFuel_terminal sound.source p hr
  have hfuelSlope : sound.source.fuel p ≤ sound.source.slopeCap := by
    calc
      sound.source.fuel p ≤ sound.source.slopeCap / p.all :=
        (min_le_right _ _).trans (min_le_right _ _)
      _ ≤ sound.source.slopeCap := Nat.div_le_self _ _
  have hfuelM : sound.source.fuel p ≤ m := hfuelSlope.trans hslopeM
  have hfuelChar : sound.source.fuel p < 2130706433 :=
    hfuelM.trans_lt hmChar
  have hlowpos : ∀ j, 1 ≤ j → j ≤ sound.source.fuel p →
      0 < D - j * 50303 := by
    intro j hj hjfuel
    have hjm : j ≤ m := hjfuel.trans hfuelM
    rw [hweighted]
    omega
  have hcapacity : ∀ j, 1 ≤ j → j ≤ sound.source.fuel p →
      D - j * 50303 ≤
        (m - j) * 181373 + j * (131071 - 1) := by
    intro j _hj hjfuel
    have hjm : j ≤ m := hjfuel.trans hfuelM
    rw [hweighted]
    omega
  have hfield : A.card < ENat.card K := by
    have hcard : A.card ≤ p.all := by
      calc
        A.card = ∑ F ∈ A, 1 := by simp
        _ ≤ ∑ F ∈ A, (regularCumulativeFlag H F).all :=
          Finset.sum_le_sum (fun F _ => Nat.one_le_iff_ne_zero.mpr
            (Nat.ne_of_gt (regularCumulativeFlag_positive H F)))
        _ = p.all := by simp only [p, regularAggregateFlag, sumFlag_all]
    calc
      (A.card : ENat) ≤ (29 : ℕ) := by
        exact_mod_cast hcard.trans hnarrowS
      _ < ENat.card K := by
        rw [ENat.card_eq_coe_fintype_card, RCN183.field_cardinality]
        norm_num
  have factor_le_aggregate (F : RegularIndex H) (hFA : F ∈ A) :
      (regularCumulativeFlag H F).all ≤ p.all ∧
      middle (regularCumulativeFlag H F) ≤ middle p ∧
      total (regularCumulativeFlag H F) ≤ total p := by
    have hsub : ({F} : Finset (RegularIndex H)) ⊆ A :=
      Finset.singleton_subset_iff.mpr hFA
    simpa [p, regularAggregateFlag, sumFlag, middle, total] using
      regularAggregateFlag_mono H hsub
  have factorFuel (F : RegularIndex H) (hFA : F ∈ A) (j : ℕ)
      (hj : j ≤ sound.source.fuel p) :
      j ≤ sound.source.fuel (regularCumulativeFlag H F) := by
    have hle := factor_le_aggregate F hFA
    have hFr : 1 ≤ (regularCumulativeFlag H F).all :=
      Nat.one_le_iff_ne_zero.mpr
        (Nat.ne_of_gt (regularCumulativeFlag_positive H F))
    have hFm : 1 ≤ middle (regularCumulativeFlag H F) :=
      hFr.trans (all_le_middle _)
    have hFt : 1 ≤ total (regularCumulativeFlag H F) :=
      hFm.trans (middle_le_total _)
    have hjT : j * total (regularCumulativeFlag H F) ≤
        sound.source.totalCap := by
      calc
        j * total (regularCumulativeFlag H F) ≤ j * total p :=
          Nat.mul_le_mul_left j hle.2.2
        _ ≤ sound.source.fuel p * total p :=
          Nat.mul_le_mul_right (total p) hj
        _ ≤ sound.source.totalCap := hfeasibleP.1
    have hjY : j * middle (regularCumulativeFlag H F) ≤
        sound.source.middleCap := by
      calc
        j * middle (regularCumulativeFlag H F) ≤ j * middle p :=
          Nat.mul_le_mul_left j hle.2.1
        _ ≤ sound.source.fuel p * middle p :=
          Nat.mul_le_mul_right (middle p) hj
        _ ≤ sound.source.middleCap := hfeasibleP.2.1
    have hjS : j * (regularCumulativeFlag H F).all ≤
        sound.source.slopeCap := by
      calc
        j * (regularCumulativeFlag H F).all ≤ j * p.all :=
          Nat.mul_le_mul_left j hle.1
        _ ≤ sound.source.fuel p * p.all :=
          Nat.mul_le_mul_right p.all hj
        _ ≤ sound.source.slopeCap := hfeasibleP.2.2
    unfold SourceNumbers.fuel
    apply le_min
    · exact (Nat.le_div_iff_mul_le hFt).mpr hjT
    · apply le_min
      · exact (Nat.le_div_iff_mul_le hFm).mpr hjY
      · exact (Nat.le_div_iff_mul_le hFr).mpr hjS
  have hgates : ∀ F ∈ A, ∀ j, j ≤ sound.source.fuel p →
      HelperPairGates
        (sound.source.totalCap - j * wt residualTotalWeights F.1)
        (sound.source.middleCap - j * wt residualYSWeights F.1)
        (sound.source.slopeCap - j * wt residualSWeights F.1)
        (wt residualYSWeights F.1) (wt residualSWeights F.1)
        (wt residualTotalWeights F.1) := by
    intro F hFA j hj
    have hc := originalCumulativeFlag_cumulative F.1
    have hle := factor_le_aggregate F hFA
    have hFr : 1 ≤ (regularCumulativeFlag H F).all :=
      Nat.one_le_iff_ne_zero.mpr
        (Nat.ne_of_gt (regularCumulativeFlag_positive H F))
    have hs := sound.stageGates (regularCumulativeFlag H F) j hFr
      (hle.1.trans hnarrowS) (hle.2.1.trans hnarrowY)
      (hle.2.2.trans hnarrowT) (factorFuel F hFA j hj)
    have hR : (regularCumulativeFlag H F).all =
        wt residualSWeights F.1 := hc.1
    have hY : middle (regularCumulativeFlag H F) =
        wt residualYSWeights F.1 := hc.2.1
    have hT : total (regularCumulativeFlag H F) =
        wt residualTotalWeights F.1 := hc.2.2
    simpa only [hR, hY, hT] using hs
  have hcharge : ∀ F ∈ A, ∀ j, j ≤ sound.source.fuel p →
      LocatorGenericPowerRoute6802.stageCost sound.source.totalCap
        sound.source.middleCap sound.source.slopeCap
        (LocatorBatchPowerRoute6802.exactRouteBox F) j ≤
          sound.potential.eval (regularCumulativeFlag H F) := by
    intro F hFA j hj
    have hc := originalCumulativeFlag_cumulative F.1
    have hle := factor_le_aggregate F hFA
    have hFr : 1 ≤ (regularCumulativeFlag H F).all :=
      Nat.one_le_iff_ne_zero.mpr
        (Nat.ne_of_gt (regularCumulativeFlag_positive H F))
    have hs := sound.stageCost_le (regularCumulativeFlag H F) j hFr
      (hle.1.trans hnarrowS) (hle.2.1.trans hnarrowY)
      (hle.2.2.trans hnarrowT) (factorFuel F hFA j hj)
    have hR : (regularCumulativeFlag H F).all =
        wt residualSWeights F.1 := hc.1
    have hY : middle (regularCumulativeFlag H F) =
        wt residualYSWeights F.1 := hc.2.1
    have hT : total (regularCumulativeFlag H F) =
        wt residualTotalWeights F.1 := hc.2.2
    simpa only [LocatorBatchPowerRoute6802.exactRouteBox,
      LocatorPhase6802Oracle.exactRouteBox, hR, hY, hT] using hs
  have hmpos : 0 < m := by omega
  have hDpos : 0 < D := by
    rw [hweighted]
    exact Nat.mul_pos hmpos (by decide)
  have hDa : D ≤ m * 181373 := hweighted.le
  apply exists_strict_helper_split_of_batch_source D
    sound.source.totalCap sound.source.slopeCap m sound.source.middleCap
    sound.source.gap 50303 (sound.source.fuel p)
  · exact hDpos
  · exact hDa
  · exact hshape
  · exact hfuel
  · exact hfuelChar
  · exact hlowpos
  · exact hcapacity
  · exact hdegree
  · exact hagreement
  · exact hno
  · exact hA
  · simpa only [SourceNumbers.band, p, regularAggregateFlag_total,
      regularAggregateFlag_middle, regularAggregateFlag_all] using
        hroute.2.2.2.2
  · simpa only [p, regularAggregateFlag_total,
      regularAggregateFlag_middle, regularAggregateFlag_all] using hterminalP
  · simpa only [p, regularAggregateFlag_total,
      regularAggregateFlag_middle, regularAggregateFlag_all] using hfeasibleP
  · exact hgap
  · exact hfield
  · exact hgates
  · exact hcharge

/-! ## State-local phase semantics

The numerical receipt is indexed by the exact aggregate raw flag.  These
lemmas keep that state intact while the algebraic route repeatedly replaces a
routeable batch by a strict universal sub-batch.
-/

/-- Raw-coordinate monotonicity of the aggregate flag. -/
theorem regularAggregateFlag_raw_mono (H : P4)
    {A B : Finset (RegularIndex H)} (hAB : A ⊆ B) :
    RawBelow (regularAggregateFlag H A) (regularAggregateFlag H B) := by
  refine ⟨?_, ?_, ?_⟩
  · change (∑ F ∈ A, (regularCumulativeFlag H F).all) ≤
      ∑ F ∈ B, (regularCumulativeFlag H F).all
    exact Finset.sum_le_sum_of_subset hAB
  · change (∑ F ∈ A, (regularCumulativeFlag H F).yz) ≤
      ∑ F ∈ B, (regularCumulativeFlag H F).yz
    exact Finset.sum_le_sum_of_subset hAB
  · change (∑ F ∈ A, (regularCumulativeFlag H F).zOnly) ≤
      ∑ F ∈ B, (regularCumulativeFlag H F).zOnly
    exact Finset.sum_le_sum_of_subset hAB

/-- An additive phase potential commutes with aggregation. -/
theorem sum_phasePotential_eval (q : Potential) (H : P4)
    (A : Finset (RegularIndex H)) :
    (∑ F ∈ A, q.eval (regularCumulativeFlag H F)) =
      q.eval (regularAggregateFlag H A) := by
  simp only [Potential.eval, Finset.sum_add_distrib, ← Finset.mul_sum,
    regularAggregateFlag, sumFlag_total, sumFlag_middle, sumFlag_all]

/-- State-local regular-seed bound used between consecutive source phases. -/
def StateLocalRegularBound (H : P4) (selected : K → Polynomial K)
    (Gamma : Finset K) (cap : FlagDegree → ℕ) : Prop :=
  ∀ A : Finset (RegularIndex H),
    (regularAggregateFlag H A).all ≤ 29 →
    middle (regularAggregateFlag H A) ≤ 132 →
    total (regularAggregateFlag H A) ≤ 6403 →
    (∑ F ∈ A, (regularSeeds H selected Gamma F).card) ≤
      cap (regularAggregateFlag H A)

/-- Ambient-scoped form needed after the initial A split.  Only factors in
the A-universal set have the narrow ordinary bound. -/
def StateLocalRegularBoundOn (H : P4) (selected : K → Polynomial K)
    (Gamma : Finset K) (ambient : Finset (RegularIndex H))
    (cap : FlagDegree → ℕ) : Prop :=
  ∀ A : Finset (RegularIndex H), A ⊆ ambient →
    (regularAggregateFlag H A).all ≤ 29 →
    middle (regularAggregateFlag H A) ≤ 132 →
    total (regularAggregateFlag H A) ≤ 6403 →
    (∑ F ∈ A, (regularSeeds H selected Gamma F).card) ≤
      cap (regularAggregateFlag H A)

/-- The state-local ordinary base restricted to an ambient factor set. -/
theorem stateLocalRegularBoundOn_of_base
    (H : P4) (selected : K → Polynomial K) (Gamma : Finset K)
    (ambient : Finset (RegularIndex H)) (baseCap : FlagDegree → ℕ)
    (hown : ∀ F ∈ ambient, LocatorHybridCostC2.OwnBoundC2
      (regularSeeds H selected Gamma F).card
      (regularCumulativeFlag H F))
    (hbase : StateLocalBaseOracleSound baseCap) :
    StateLocalRegularBoundOn H selected Gamma ambient baseCap := by
  classical
  intro A hAambient hs hy ht
  calc
    (∑ F ∈ A, (regularSeeds H selected Gamma F).card) ≤
        ∑ F ∈ A,
          LocatorHybridCostC2.ordinaryCostOfC2 (regularCumulativeFlag H F) :=
      Finset.sum_le_sum (fun F hFA =>
        LocatorHybridCostC2.ownBound_le_ordinaryCostOfC2
          (hown F (hAambient hFA)))
    _ ≤ baseCap (regularAggregateFlag H A) := by
      simpa only [regularAggregateFlag] using
        hbase A (regularCumulativeFlag H)
          (fun F _hF => Nat.one_le_iff_ne_zero.mpr
            (Nat.ne_of_gt (regularCumulativeFlag_positive H F))) hs hy ht

/-- The state-local ordinary partition oracle starts the four phase chain. -/
theorem stateLocalRegularBound_of_base
    (H : P4) (selected : K → Polynomial K) (Gamma : Finset K)
    (baseCap : FlagDegree → ℕ)
    (hown : ∀ F, LocatorHybridCostC2.OwnBoundC2
      (regularSeeds H selected Gamma F).card
      (regularCumulativeFlag H F))
    (hbase : StateLocalBaseOracleSound baseCap) :
    StateLocalRegularBound H selected Gamma baseCap := by
  classical
  intro A hs hy ht
  calc
    (∑ F ∈ A, (regularSeeds H selected Gamma F).card) ≤
        ∑ F ∈ A,
          LocatorHybridCostC2.ordinaryCostOfC2 (regularCumulativeFlag H F) :=
      Finset.sum_le_sum (fun F _hF =>
        LocatorHybridCostC2.ownBound_le_ordinaryCostOfC2 (hown F))
    _ ≤ baseCap (regularAggregateFlag H A) := by
      simpa only [regularAggregateFlag] using
        hbase A (regularCumulativeFlag H)
          (fun F _hF => Nat.one_le_iff_ne_zero.mpr
            (Nat.ne_of_gt (regularCumulativeFlag_positive H F))) hs hy ht

/-- Concrete kernel realization of one numerical source. -/
structure PhaseKernelRealization (sound : PhaseSourceSound)
    (u0 u1 : I → K) where
  D : ℕ
  m : ℕ
  weighted : D = m * 181373
  shape : D + sound.source.slopeCap ≤
    131071 * (sound.source.middleCap + 1)
  slope_le_m : sound.source.slopeCap ≤ m
  m_lt_char : m < 2130706433
  gap_le_finrank : sound.source.gap ≤ Module.finrank K
    (ConstraintKernel (K := K) D 131071 sound.source.totalCap
      sound.source.slopeCap m IRSProfile.domain u0 u1)

/-- One source phase preserves a state-local bound according to the numeric
cap equation.  The only recursive calls are on strict factor subsets, hence
the receipt defect is queried at a strict raw-slope child of the parent. -/
theorem stateLocalRegularBoundOn_onePhase
    (sound : PhaseSourceSound) (u0 u1 : I → K)
    (kernel : PhaseKernelRealization sound u0 u1)
    (H : P4) (selected : K → Polynomial K) (Gamma : Finset K)
    (ambient : Finset (RegularIndex H))
    (hdegree : ∀ gamma ∈ Gamma,
      (selected gamma).natDegree ≤ 131071)
    (hagreement : ∀ gamma ∈ Gamma, 181373 ≤
      ((Finset.univ : Finset I).filter (fun i ↦
        (selected gamma).eval (IRSProfile.domain i) =
          u0 i + gamma * u1 i)).card)
    (hno : NoLargeSelectedPencil selected Gamma 131071 80771)
    (previousCap nextCap defect : FlagDegree → ℕ)
    (hprevious : StateLocalRegularBoundOn H selected Gamma ambient previousCap)
    (hdefect : PhaseDefectSound previousCap sound.source
      sound.potential defect)
    (hcap : PhaseCapEquation previousCap nextCap sound.source
      sound.potential defect) :
    StateLocalRegularBoundOn H selected Gamma ambient nextCap := by
  classical
  intro A hAambient hs hy ht
  let p := regularAggregateFlag H A
  have hpreviousA :
      (∑ F ∈ A, (regularSeeds H selected Gamma F).card) ≤ previousCap p :=
    hprevious A hAambient hs hy ht
  have hcapP := hcap p hs hy ht
  by_cases hrouteP : sound.source.Routeable p
  · have hphase :
        (∑ F ∈ A, (regularSeeds H selected Gamma F).card) ≤
          min (previousCap p)
            ((∑ F ∈ A,
              sound.potential.eval (regularCumulativeFlag H F)) + defect p) := by
      apply sum_count_le_min_previous_onePhase
        (fun F : RegularIndex H =>
          (regularSeeds H selected Gamma F).card)
        (fun F : RegularIndex H =>
          sound.potential.eval (regularCumulativeFlag H F))
        (fun B : Finset (RegularIndex H) =>
          sound.source.Routeable (regularAggregateFlag H B))
        (fun B : Finset (RegularIndex H) =>
          previousCap (regularAggregateFlag H B)) A (defect p)
      · intro B hBA
        have hmono := regularAggregateFlag_mono H hBA
        exact hprevious B (hBA.trans hAambient)
          (hmono.1.trans hs) (hmono.2.1.trans hy)
          (hmono.2.2.trans ht)
      · intro B hBA hnrouteB
        have hne : B ≠ A := by
          intro hBAeq
          subst B
          exact hnrouteB hrouteP
        have hproper : B ⊂ A :=
          (_root_.ssubset_iff_subset_ne).mpr ⟨hBA, hne⟩
        have hd := hdefect p (regularAggregateFlag H B) hs hy ht
          ⟨regularAggregateFlag_raw_mono H hBA,
            regularAggregateFlag_all_lt_of_ssubset H hproper⟩ hnrouteB
        rw [← sum_phasePotential_eval sound.potential H B] at hd
        exact hd
      · intro B hBA hrouteB
        have hmono := regularAggregateFlag_mono H hBA
        obtain ⟨U, hUB, hexit⟩ :=
          routeable_exists_strict_helper_split sound kernel.D kernel.m
            kernel.weighted kernel.shape kernel.slope_le_m kernel.m_lt_char
            u0 u1 H selected Gamma hdegree hagreement hno
            kernel.gap_le_finrank B hrouteB
            (hmono.1.trans hs) (hmono.2.1.trans hy)
            (hmono.2.2.trans ht)
        refine ⟨U, hUB, ?_⟩
        exact Finset.sum_le_sum (fun F hFU => hexit F hFU)
    rw [hcapP, if_pos hrouteP]
    simpa only [p, sum_phasePotential_eval] using hphase
  · rw [hcapP, if_neg hrouteP]
    exact hpreviousA

/-- Unscoped convenience corollary. -/
theorem stateLocalRegularBound_onePhase
    (sound : PhaseSourceSound) (u0 u1 : I → K)
    (kernel : PhaseKernelRealization sound u0 u1)
    (H : P4) (selected : K → Polynomial K) (Gamma : Finset K)
    (hdegree : ∀ gamma ∈ Gamma,
      (selected gamma).natDegree ≤ 131071)
    (hagreement : ∀ gamma ∈ Gamma, 181373 ≤
      ((Finset.univ : Finset I).filter (fun i ↦
        (selected gamma).eval (IRSProfile.domain i) =
          u0 i + gamma * u1 i)).card)
    (hno : NoLargeSelectedPencil selected Gamma 131071 80771)
    (previousCap nextCap defect : FlagDegree → ℕ)
    (hprevious : StateLocalRegularBound H selected Gamma previousCap)
    (hdefect : PhaseDefectSound previousCap sound.source
      sound.potential defect)
    (hcap : PhaseCapEquation previousCap nextCap sound.source
      sound.potential defect) :
    StateLocalRegularBound H selected Gamma nextCap := by
  have hpreviousOn : StateLocalRegularBoundOn H selected Gamma
      (Finset.univ : Finset (RegularIndex H)) previousCap := by
    intro A _hA hs hy ht
    exact hprevious A hs hy ht
  have hnext := stateLocalRegularBoundOn_onePhase sound u0 u1 kernel H
    selected Gamma (Finset.univ : Finset (RegularIndex H)) hdegree
    hagreement hno previousCap nextCap defect hpreviousOn hdefect hcap
  intro A hs hy ht
  exact hnext A (fun _ _ ↦ Finset.mem_univ _) hs hy ht

end

end ProximityPrize.SubmissionLower.LocatorBatchPhase6802
