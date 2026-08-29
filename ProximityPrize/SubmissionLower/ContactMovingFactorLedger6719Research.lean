import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactMovingPositiveLedger6719Research
import ProximityPrize.SubmissionLower.ContactGCDCumulativeLedgerResearch

/-! .
 -/

namespace ProximityPrize.SubmissionLower.ContactMovingFactorLedger6719Research

open scoped Classical BigOperators
open ContactFlagBezout6543Research ContactMovingPositiveLedger6719Research
open ContactRobustFixedMeet6656Research ContactGCDCumulativeFlagsResearch
open ContactOriginalRegularSeedCount ContactRegularFactorFlag6600Research
open ContactResidualSupportParametersResearch ContactTranslation

noncomputable section
set_option maxHeartbeats 2000000

def factorDegreeCost (p : Profile) (a b s : ℕ) (flag : FlagDegree) : ℕ :=
  p.degreeIncidence * qeff a b s flag + p.unitIncidence * lin a b s flag +
    (p.errors+1)*p.gap*(zSlope a b s flag + yzSlope a b s flag)

def factorUnitCost (p : Profile) (a b s : ℕ) (flag : FlagDegree) : ℕ :=
  p.degreeIncidence * lin a b s flag + p.unitIncidence * unit a b s flag +
    (p.errors+1)*p.gap*(zBase a b s flag + yzBase a b s flag)

def regularLedger (p : Profile) (a b s : ℕ) (flag : FlagDegree) : ℕ :=
  p.degreeIncidence * factorDegreeCost p a b s flag +
    p.unitIncidence * factorUnitCost p a b s flag

theorem regularLedger_expanded (p : Profile) (a b s : ℕ) (flag : FlagDegree) :
    regularLedger p a b s flag =
      qeff a b s flag * p.degreeIncidence^2 +
        2 * lin a b s flag * p.degreeIncidence * p.unitIncidence +
        unit a b s flag * p.unitIncidence^2 +
        (p.errors+1)*p.gap*(zSlope a b s flag*p.degreeIncidence + zBase a b s flag*p.unitIncidence) +
        (p.errors+1)*p.gap*(yzSlope a b s flag*p.degreeIncidence + yzBase a b s flag*p.unitIncidence) := by
  simp only [regularLedger, factorDegreeCost, factorUnitCost]
  ring

/-- .
 -/
theorem sum_regularLedger_le {I : Type*} [Fintype I]
    (p : Profile) (a b s : ℕ) (flags : I → FlagDegree) (cap : FlagDegree)
    (hi : (∑ i, (flags i).all) ≤ cap.all)
    (hm : (∑ i, ((flags i).yz+(flags i).all)) ≤ cap.yz+cap.all)
    (ht : (∑ i, ((flags i).zOnly+(flags i).yz+(flags i).all)) ≤
      cap.zOnly+cap.yz+cap.all) :
    (∑ i, regularLedger p a b s (flags i)) ≤ regularLedger p a b s cap := by
  simp only [regularLedger, factorDegreeCost, factorUnitCost,
    Finset.sum_add_distrib, ← Finset.mul_sum]
  gcongr
  all_goals first
    | exact sum_qeff_le flags cap hi hm ht a b s
    | exact sum_lin_le flags cap hi hm ht a b s
    | exact sum_unit_le flags cap hi hm ht a b s
    | exact sum_zSlope_le flags cap hi hm ht a b s
    | exact sum_yzSlope_le flags cap hi hm ht a b s
    | exact sum_zBase_le flags cap hi hm ht a b s
    | exact sum_yzBase_le flags cap hi hm ht a b s

variable {K : Type} [Field K]

theorem sum_regular_counts_le
    (p : Profile) (a b s : ℕ)
    (Q : MvPolynomial (Fin 4) K) (hQ : Q ≠ 0)
    {support : ResidualSupportParameters} (H : ResidualSupportData support Q)
    (count : RegularIndex Q → ℕ)
    (hcount : ∀ R, count R*p.gap^2 ≤ regularLedger p a b s (regularCumulativeFlag Q R)) :
    (∑ R, count R)*p.gap^2 ≤ regularLedger p a b s (supportCumulativeFlag support) := by
  have hc := regularCumulativeFlag_budgets Q hQ H
  have hp := flagFromCaps_cumulative support.total support.ys support.s
    support.s_le_ys support.ys_le_total
  calc
    _ = ∑ R, count R*p.gap^2 := by rw [Finset.sum_mul]
    _ ≤ ∑ R, regularLedger p a b s (regularCumulativeFlag Q R) :=
      Finset.sum_le_sum (fun R _ ↦ hcount R)
    _ ≤ _ := sum_regularLedger_le p a b s (regularCumulativeFlag Q)
      (supportCumulativeFlag support)
      (by simpa only [supportCumulativeFlag, hp.1] using hc.1)
      (by simpa only [supportCumulativeFlag, hp.2.1] using hc.2.1)
      (by simpa only [supportCumulativeFlag, hp.2.2] using hc.2.2)

theorem geometric_seed_counts_le
    (p : Profile) (a b s : ℕ)
    (F : MvPolynomial (Fin 4) K) (hF : F ≠ 0)
    (selected : K → Polynomial K) (Γ : Finset K)
    (hsolutions : ∀ γ ∈ Γ, specialization K (selected γ) γ F = 0)
    (hcount : ∀ g : GeometricFactor K F,
      (geometricSeeds K F selected Γ g).card*p.gap^2 ≤
        regularLedger p a b s (geometricCumulativeFlag K g)) :
    Γ.card*p.gap^2 ≤ regularLedger p a b s (originalCumulativeFlag F) := by
  have hc := geometricCumulativeFlag_budgets F hF
  calc
    _ ≤ (∑ g : GeometricFactor K F, (geometricSeeds K F selected Γ g).card)*p.gap^2 :=
      Nat.mul_le_mul_right _ (card_le_sum_geometricSeeds K F hF selected Γ hsolutions)
    _ = ∑ g : GeometricFactor K F, (geometricSeeds K F selected Γ g).card*p.gap^2 :=
      by rw [Finset.sum_mul]
    _ ≤ ∑ g : GeometricFactor K F, regularLedger p a b s (geometricCumulativeFlag K g) :=
      Finset.sum_le_sum (fun g _ ↦ hcount g)
    _ ≤ _ := sum_regularLedger_le p a b s (geometricCumulativeFlag K)
      (originalCumulativeFlag F) hc.1 hc.2.1 hc.2.2

end

end ProximityPrize.SubmissionLower.ContactMovingFactorLedger6719Research
