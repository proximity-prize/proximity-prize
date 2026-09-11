import ProximityPrize.SubmissionLower.PartG005


section Compact_BatchPhase80791
/-! Error-80791 phase ingredient, adapted from the promoted shared-product machinery.
No protocol claim is asserted in this module. -/
set_option Elab.async false
namespace ProximityPrize.SubmissionLower.Lower80791.BatchPhase

open ProximityPrize.Benchmark
open scoped BigOperators
open RCN071 RCN081 RCN095 RCN100 RCN101 RCN119 RCN130 RCN140 RCN156
  RCN180 RCN234 RCN238 RCN260 RCN266
open LocatorFactorAggregate LocatorArbitraryPowerAvoidance
  LocatorBatchProductRoute Lower80791.BatchPowerRoute
  Lower80791.FactorSwitch Lower80791.Oracle

open LocatorPhase6800Oracle (Potential sumFlag sumFlag_all sumFlag_middle sumFlag_total RawBelow RawStrictSlopeBelow)
open LocatorBatchPhase6800 (regularAggregateFlag regularAggregateFlag_all
  regularAggregateFlag_middle regularAggregateFlag_total regularAggregateFlag_mono
  regularAggregateFlag_all_lt_of_ssubset regularAggregateFlag_raw_mono sum_phasePotential_eval)

noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

abbrev K := IRSProfile.Field
abbrev I := IRSProfile.Index
abbrev P4 := MvPolynomial (Fin 4) K

local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I

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
    (hweighted : D = m * 181353)
    (hshape : D + sound.source.slopeCap ≤
      131071 * (sound.source.middleCap + 1))
    (hslopeM : sound.source.slopeCap ≤ m)
    (hmChar : m < 2130706433)
    (u0 u1 : I → K) (H : P4)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hdegree : ∀ gamma ∈ Gamma,
      (selected gamma).natDegree ≤ 131071)
    (hagreement : ∀ gamma ∈ Gamma, 181353 ≤
      ((Finset.univ : Finset I).filter (fun i ↦
        (selected gamma).eval (IRSProfile.domain i) =
          u0 i + gamma * u1 i)).card)
    (hno : NoLargeSelectedPencil selected Gamma 131071 80791)
    (hgap : sound.source.gap ≤ Module.finrank K
      (ConstraintKernel (K := K) D 131071 sound.source.totalCap
        sound.source.slopeCap m IRSProfile.domain u0 u1))
    (A : Finset (RegularIndex H))
    (hroute : sound.source.Routeable (regularAggregateFlag H A))
    (hnarrowS : (regularAggregateFlag H A).all ≤ 30)
    (hnarrowY : middle (regularAggregateFlag H A) ≤ 136)
    (hnarrowT : total (regularAggregateFlag H A) ≤ 6917) :
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
      0 < D - j * 50283 := by
    intro j hj hjfuel
    have hjm : j ≤ m := hjfuel.trans hfuelM
    rw [hweighted]
    omega
  have hcapacity : ∀ j, 1 ≤ j → j ≤ sound.source.fuel p →
      D - j * 50283 ≤
        (m - j) * 181353 + j * (131071 - 1) := by
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
      (A.card : ENat) ≤ (30 : ℕ) := by
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
      Lower80791.PowerRoute.stageCost sound.source.totalCap
        sound.source.middleCap sound.source.slopeCap
        (Lower80791.BatchPowerRoute.exactRouteBox F) j ≤
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
    simpa only [Lower80791.BatchPowerRoute.exactRouteBox,
      Lower80791.Oracle.exactRouteBox, hR, hY, hT] using hs
  have hmpos : 0 < m := by omega
  have hDpos : 0 < D := by
    rw [hweighted]
    exact Nat.mul_pos hmpos (by decide)
  have hDa : D ≤ m * 181353 := hweighted.le
  have hP : regularProduct H A ≠ 0 := regularProduct_ne_zero H A
  have hcP : contactDec p ≤ wt (contactWeights 131071) (regularProduct H A) := by
    have h := LocatorArbitraryPowerAvoidance.contact_ge_ys 131071 (by decide)
      (regularProduct H A) hP
    simpa only [contactDec, p, regularAggregateFlag_middle,
      regularAggregateFlag_all] using h
  have hDcap : D - wt (contactWeights 131071) (regularProduct H A) ≤
      sound.source.contactCap p := by
    unfold SourceNumbers.contactCap
    omega
  have hbandThin : LocatorArbitraryPowerAvoidance.powerBandBudgetThin 131071
      (D - wt (contactWeights 131071) (regularProduct H A)) 50283
      (wt (contactWeights 131071) (regularProduct H A))
      (wt residualTotalWeights (regularProduct H A))
      (wt residualYSWeights (regularProduct H A))
      (wt residualSWeights (regularProduct H A))
      (sound.source.totalCap - wt residualTotalWeights (regularProduct H A))
      (sound.source.middleCap - wt residualYSWeights (regularProduct H A))
      (sound.source.slopeCap - wt residualSWeights (regularProduct H A))
      (sound.source.fuel p) < sound.source.gap := by
    rcases hroute.2.2.2.2 with hold | hthin
    · have hold' : powerBandBudget 50283
          (wt residualTotalWeights (regularProduct H A))
          (wt residualYSWeights (regularProduct H A))
          (wt residualSWeights (regularProduct H A))
          (sound.source.totalCap - wt residualTotalWeights (regularProduct H A))
          (sound.source.middleCap - wt residualYSWeights (regularProduct H A))
          (sound.source.slopeCap - wt residualSWeights (regularProduct H A))
          (sound.source.fuel p) < sound.source.gap := by
        simpa only [SourceNumbers.band, p, regularAggregateFlag_total,
          regularAggregateFlag_middle, regularAggregateFlag_all] using hold
      exact (LocatorArbitraryPowerAvoidance.powerBandBudgetThin_le
        _ _ _ _ _ _ _ _ _ _ _).trans_lt hold'
    · have hthin' : LocatorArbitraryPowerAvoidance.powerBandBudgetThin 131071
          (sound.source.contactCap p) 50283 (contactDec p)
          (wt residualTotalWeights (regularProduct H A))
          (wt residualYSWeights (regularProduct H A))
          (wt residualSWeights (regularProduct H A))
          (sound.source.totalCap - wt residualTotalWeights (regularProduct H A))
          (sound.source.middleCap - wt residualYSWeights (regularProduct H A))
          (sound.source.slopeCap - wt residualSWeights (regularProduct H A))
          (sound.source.fuel p) < sound.source.gap := by
        simpa only [SourceNumbers.bandThin, p, regularAggregateFlag_total,
          regularAggregateFlag_middle, regularAggregateFlag_all] using hthin
      exact (LocatorArbitraryPowerAvoidance.powerBandBudgetThin_mono 131071 50283
        (sound.source.fuel p) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
        hDcap hcP le_rfl le_rfl le_rfl le_rfl le_rfl le_rfl).trans_lt hthin'
  apply exists_strict_helper_split_of_batch_source_thin D
    sound.source.totalCap sound.source.slopeCap m sound.source.middleCap
    sound.source.gap 50283 (sound.source.fuel p)
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
  · exact hbandThin
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

/-- State-local regular-seed bound used between consecutive source phases. -/
def StateLocalRegularBound (H : P4) (selected : K → Polynomial K)
    (Gamma : Finset K) (cap : FlagDegree → ℕ) : Prop :=
  ∀ A : Finset (RegularIndex H),
    (regularAggregateFlag H A).all ≤ 30 →
    middle (regularAggregateFlag H A) ≤ 136 →
    total (regularAggregateFlag H A) ≤ 6917 →
    (∑ F ∈ A, (regularSeeds H selected Gamma F).card) ≤
      cap (regularAggregateFlag H A)

/-- Ambient-scoped form needed after the initial A split.  Only factors in
the A-universal set have the narrow ordinary bound. -/
def StateLocalRegularBoundOn (H : P4) (selected : K → Polynomial K)
    (Gamma : Finset K) (ambient : Finset (RegularIndex H))
    (cap : FlagDegree → ℕ) : Prop :=
  ∀ A : Finset (RegularIndex H), A ⊆ ambient →
    (regularAggregateFlag H A).all ≤ 30 →
    middle (regularAggregateFlag H A) ≤ 136 →
    total (regularAggregateFlag H A) ≤ 6917 →
    (∑ F ∈ A, (regularSeeds H selected Gamma F).card) ≤
      cap (regularAggregateFlag H A)

/-- Concrete kernel realization of one numerical source. -/
structure PhaseKernelRealization (sound : PhaseSourceSound)
    (u0 u1 : I → K) where
  D : ℕ
  m : ℕ
  weighted : D = m * 181353
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
    (hagreement : ∀ gamma ∈ Gamma, 181353 ≤
      ((Finset.univ : Finset I).filter (fun i ↦
        (selected gamma).eval (IRSProfile.domain i) =
          u0 i + gamma * u1 i)).card)
    (hno : NoLargeSelectedPencil selected Gamma 131071 80791)
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
    (hagreement : ∀ gamma ∈ Gamma, 181353 ≤
      ((Finset.univ : Finset I).filter (fun i ↦
        (selected gamma).eval (IRSProfile.domain i) =
          u0 i + gamma * u1 i)).card)
    (hno : NoLargeSelectedPencil selected Gamma 131071 80791)
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

end ProximityPrize.SubmissionLower.Lower80791.BatchPhase

end Compact_BatchPhase80791
