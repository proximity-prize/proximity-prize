import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactGCDCumulativeFlagsResearch
import ProximityPrize.SubmissionLower.ContactProfileYZFactorLedgerResearch

/-! Cumulative aggregation for the actual sharp-YZ regular-factor ledger. -/

namespace ProximityPrize.SubmissionLower.ContactGCDCumulativeLedgerResearch

open scoped Classical BigOperators
open ContactFlagBezout6543Research ContactGCDCumulativeFlagsResearch
open ContactProfileYZFactorLedgerResearch ContactRobustFixedMeet6656Research
open ContactRegularFactorFlag6600Research ContactOriginalRegularSeedCount
open ContactResidualSupportParametersResearch ContactInterpolation ContactTranslation

noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 30000

/-- Nested unit polytopes have increasing mixed-volume coefficients. -/
theorem flagMixed_unit_mono (q r : FlagDegree) :
    flagMixed unitZFlag q r ≤ flagMixed unitYZFlag q r ∧
      flagMixed unitYZFlag q r ≤ flagMixed unitAllFlag q r := by
  constructor
  · calc
      flagMixed unitZFlag q r ≤ flagMixed unitZFlag q r +
          (q.zOnly * r.all + r.zOnly * q.all) := Nat.le_add_right _ _
      _ = flagMixed unitYZFlag q r := by
        simp [flagMixed, unitZFlag, unitYZFlag]
        ring
  · calc
      flagMixed unitYZFlag q r ≤ flagMixed unitYZFlag q r +
          (q.yz * r.yz + q.zOnly * r.yz + r.zOnly * q.yz) := Nat.le_add_right _ _
      _ = flagMixed unitAllFlag q r := by
        simp [flagMixed, unitYZFlag, unitAllFlag]
        ring

theorem ledger_unit_mono (p : Profile) (direction : FlagDegree) :
    factorRegularLedgerYZForDirection p direction unitZFlag ≤
        factorRegularLedgerYZForDirection p direction unitYZFlag ∧
      factorRegularLedgerYZForDirection p direction unitYZFlag ≤
        factorRegularLedgerYZForDirection p direction unitAllFlag := by
  have hm (a b : FlagDegree)
      (h : ∀ q r, flagMixed a q r ≤ flagMixed b q r) :
      factorRegularLedgerYZForDirection p direction a ≤
        factorRegularLedgerYZForDirection p direction b := by
    unfold factorRegularLedgerYZForDirection factorPrimaryForDirection
      factorZTailForDirection factorYZTailForDirection
    gcongr <;> exact h _ _
  exact ⟨hm _ _ (fun q r ↦ (flagMixed_unit_mono q r).1),
    hm _ _ (fun q r ↦ (flagMixed_unit_mono q r).2)⟩

theorem linear_cost_cumulative (cz cy ca : ℕ) (f : FlagDegree)
    (hzy : cz ≤ cy) (hya : cy ≤ ca) :
    f.zOnly * cz + f.yz * cy + f.all * ca =
      cz * (f.zOnly + f.yz + f.all) +
        (cy - cz) * (f.yz + f.all) + (ca - cy) * f.all := by
  have hy : cz + (cy - cz) = cy := by omega
  have ha : cz + (cy - cz) + (ca - cy) = ca := by omega
  calc
    f.zOnly * cz + f.yz * cy + f.all * ca =
        f.zOnly * cz + f.yz * (cz + (cy - cz)) +
          f.all * (cz + (cy - cz) + (ca - cy)) := by rw [ha, hy]
    _ = _ := by ring

/-- Any flag-linear functional with increasing unit coefficients is
monotone under cumulative, not necessarily coordinatewise, sum bounds. -/
theorem sum_linear_cost_cumulative_le
    {I : Type} [Fintype I] (cost : FlagDegree → ℕ)
    (hlinear : ∀ f, cost f = f.zOnly * cost unitZFlag +
      f.yz * cost unitYZFlag + f.all * cost unitAllFlag)
    (hzy : cost unitZFlag ≤ cost unitYZFlag)
    (hya : cost unitYZFlag ≤ cost unitAllFlag)
    (flag : I → FlagDegree) (cap : FlagDegree)
    (hi : (∑ i, (flag i).all) ≤ cap.all)
    (hm : (∑ i, ((flag i).yz + (flag i).all)) ≤ cap.yz + cap.all)
    (ht : (∑ i, ((flag i).zOnly + (flag i).yz + (flag i).all)) ≤
      cap.zOnly + cap.yz + cap.all) :
    (∑ i, cost (flag i)) ≤ cost cap := by
  have heq (f : FlagDegree) : cost f =
      cost unitZFlag * (f.zOnly + f.yz + f.all) +
        (cost unitYZFlag - cost unitZFlag) * (f.yz + f.all) +
        (cost unitAllFlag - cost unitYZFlag) * f.all := by
    rw [hlinear f]
    exact linear_cost_cumulative _ _ _ f hzy hya
  rw [Finset.sum_congr rfl (fun i _ ↦ heq (flag i)), heq cap]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  simpa only [Finset.sum_add_distrib] using Nat.add_le_add
    (Nat.add_le_add (Nat.mul_le_mul_left _ ht) (Nat.mul_le_mul_left _ hm))
    (Nat.mul_le_mul_left _ hi)

theorem sum_ledger_cumulative_le
    {I : Type} [Fintype I] (p : Profile) (direction : FlagDegree)
    (flag : I → FlagDegree) (cap : FlagDegree)
    (hi : (∑ i, (flag i).all) ≤ cap.all)
    (hm : (∑ i, ((flag i).yz + (flag i).all)) ≤ cap.yz + cap.all)
    (ht : (∑ i, ((flag i).zOnly + (flag i).yz + (flag i).all)) ≤
      cap.zOnly + cap.yz + cap.all) :
    (∑ i, factorRegularLedgerYZForDirection p direction (flag i)) ≤
      factorRegularLedgerYZForDirection p direction cap :=
  sum_linear_cost_cumulative_le (factorRegularLedgerYZForDirection p direction)
    (factorRegularLedgerYZForDirection_projection_decomposition p direction)
    (ledger_unit_mono p direction).1 (ledger_unit_mono p direction).2
    flag cap hi hm ht

variable {K : Type} [Field K]

/-- The actual original factor counts consume the sharp support flag. -/
theorem sum_regular_counts_cumulative_le
    (p : Profile) (direction : FlagDegree)
    (Q : MvPolynomial (Fin 4) K) (hQ : Q ≠ 0)
    {P : ResidualSupportParameters} (H : ResidualSupportData P Q)
    (count : RegularIndex Q → ℕ)
    (hcount : ∀ R, count R * p.gap ^ 2 ≤
      factorRegularLedgerYZForDirection p direction (regularCumulativeFlag Q R)) :
    (∑ R, count R) * p.gap ^ 2 ≤
      factorRegularLedgerYZForDirection p direction (supportCumulativeFlag P) := by
  have hc := regularCumulativeFlag_budgets Q hQ H
  have hp := flagFromCaps_cumulative P.total P.ys P.s P.s_le_ys P.ys_le_total
  calc
    (∑ R, count R) * p.gap ^ 2 = ∑ R, count R * p.gap ^ 2 := by rw [Finset.sum_mul]
    _ ≤ ∑ R, factorRegularLedgerYZForDirection p direction
        (regularCumulativeFlag Q R) := Finset.sum_le_sum (fun R _ ↦ hcount R)
    _ ≤ factorRegularLedgerYZForDirection p direction (supportCumulativeFlag P) :=
      sum_ledger_cumulative_le p direction (regularCumulativeFlag Q)
        (supportCumulativeFlag P)
        (by simpa only [supportCumulativeFlag, hp.1] using hc.1)
        (by simpa only [supportCumulativeFlag, hp.2.1] using hc.2.1)
        (by simpa only [supportCumulativeFlag, hp.2.2] using hc.2.2)

/-- The existing geometric selected-point cover and actual product budgets
aggregate without changing either the factors or the selected solutions. -/
theorem geometric_seed_counts_cumulative_le
    (p : Profile) (direction : FlagDegree)
    (F : MvPolynomial (Fin 4) K) (hF : F ≠ 0)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hsolutions : ∀ gamma ∈ Gamma,
      specialization K (selected gamma) gamma F = 0)
    (hcount : ∀ g : GeometricFactor K F,
      (geometricSeeds K F selected Gamma g).card * p.gap ^ 2 ≤
        factorRegularLedgerYZForDirection p direction (geometricCumulativeFlag K g)) :
    Gamma.card * p.gap ^ 2 ≤
      factorRegularLedgerYZForDirection p direction (originalCumulativeFlag F) := by
  have hc := geometricCumulativeFlag_budgets F hF
  calc
    Gamma.card * p.gap ^ 2 ≤
        (∑ g : GeometricFactor K F, (geometricSeeds K F selected Gamma g).card) *
          p.gap ^ 2 := Nat.mul_le_mul_right _
            (card_le_sum_geometricSeeds K F hF selected Gamma hsolutions)
    _ = ∑ g : GeometricFactor K F,
        (geometricSeeds K F selected Gamma g).card * p.gap ^ 2 := by rw [Finset.sum_mul]
    _ ≤ ∑ g : GeometricFactor K F,
        factorRegularLedgerYZForDirection p direction (geometricCumulativeFlag K g) :=
      Finset.sum_le_sum (fun g _ ↦ hcount g)
    _ ≤ factorRegularLedgerYZForDirection p direction (originalCumulativeFlag F) :=
      sum_ledger_cumulative_le p direction (geometricCumulativeFlag K)
        (originalCumulativeFlag F) hc.1 hc.2.1 hc.2.2

end
end ProximityPrize.SubmissionLower.ContactGCDCumulativeLedgerResearch
