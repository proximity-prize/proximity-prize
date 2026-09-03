import ProximityPrize.SubmissionLower.LocatorFifthPowerAvoidance
import ProximityPrize.SubmissionLower.LocatorQuotientMonotone

/-!
# Arbitrarily many successive locator quotient projections

This is the recursive form of the explicitly unrolled second-through-ninth
power-avoidance lemmas.  It deliberately concerns only the linear high-band
selection.  Contact-order vanishing and extraction of the terminal quotient
from an iterated derivative are independent consumers of the witness returned
here.
-/

namespace ProximityPrize.SubmissionLower.LocatorArbitraryPowerAvoidance

open scoped BigOperators
open RCN081 RCN100 RCN119 RCN130 RCN156 RCN180 RCN234 RCN260
open LocatorLowQuotient LocatorCoprimeQuotient
  LocatorDoubleSquareAvoidance

noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

variable {K V : Type*} [Field K]
local instance : DecidableEq K := Classical.decEq K

abbrev P4 (K : Type*) [Field K] := MvPolynomial (Fin 4) K

/-- The exact cumulative cost of `k` successive high-band projections.
The decrement form is chosen so that removing the first projection is
definitionally the same budget at the shifted quotient box. -/
def powerBandBudget
    (delta dT dY dS T YS S : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 =>
      delta * channelCount T YS S +
        powerBandBudget delta dT dY dS
          (T - dT) (YS - dY) (S - dS) k

/-- Enlarging the current box and decreasing its per-stage losses can only
increase the cumulative high-band budget. -/
theorem powerBandBudget_mono
    (delta dT₁ dY₁ dS₁ T₁ Y₁ S₁ dT₂ dY₂ dS₂ T₂ Y₂ S₂ k : ℕ)
    (hT : T₁ ≤ T₂) (hY : Y₁ ≤ Y₂) (hS : S₁ ≤ S₂)
    (hdT : dT₂ ≤ dT₁) (hdY : dY₂ ≤ dY₁)
    (hdS : dS₂ ≤ dS₁) :
    powerBandBudget delta dT₁ dY₁ dS₁ T₁ Y₁ S₁ k ≤
      powerBandBudget delta dT₂ dY₂ dS₂ T₂ Y₂ S₂ k := by
  induction k generalizing T₁ Y₁ S₁ T₂ Y₂ S₂ with
  | zero =>
      simp only [powerBandBudget]
      exact Nat.zero_le _
  | succ k ih =>
      simp only [powerBandBudget]
      apply Nat.add_le_add
      · exact Nat.mul_le_mul_left delta (channelCount_mono hT hY hS)
      · apply ih
        · omega
        · omega
        · omega

/-- After `steps + 1` high-band projections, some nonzero member of the
source family has an `F`-adic stage `j`.  A nonterminal stage is coprime to
`F`; the last stage is allowed to remain divisible because the consumer uses
its terminal weight inequality instead.

The stage is represented by `j : Fin (steps + 1)`.  Thus the returned source
identity is `F ^ j * J = q v`, while the corresponding original reconstructed
row (which already has one outer factor `F`) is `F ^ (j+1) * J`.
-/
theorem exists_power_stage_of_bandBudget_succ
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (steps Dhigh Dlow w delta T YS S : ℕ)
    (hwidth : Dhigh ≤ Dlow + delta)
    (q : V →ₗ[K] P4 K) (hq : Function.Injective q)
    (hmem : ∀ v, q v ∈ nestedCoefficientBox K Dhigh w T YS S)
    (F : P4 K) (hF : F ≠ 0)
    (hsource :
      powerBandBudget delta
          (wt residualTotalWeights F) (wt residualYSWeights F)
          (wt residualSWeights F) T YS S (steps + 1) <
        Module.finrank K V) :
    ∃ (j : Fin (steps + 1)) (v : V) (J : P4 K),
      v ≠ 0 ∧ J ≠ 0 ∧ F ^ j.val * J = q v ∧
      J ∈ nestedCoefficientBox K
        (Dlow - j.val * delta - j.val * wt (contactWeights w) F) w
        (T - j.val * wt residualTotalWeights F)
        (YS - j.val * wt residualYSWeights F)
        (S - j.val * wt residualSWeights F) ∧
      (j.val + 1 < steps + 1 → ¬ F ∣ J) := by
  classical
  induction steps generalizing V Dhigh Dlow T YS S with
  | zero =>
      have hfirst : delta * channelCount T YS S < Module.finrank K V := by
        simpa only [powerBandBudget, Nat.add_zero] using hsource
      obtain ⟨v, hv, hqv, hlow⟩ :=
        exists_nonzero_image_mem_low Dhigh Dlow w delta T YS S hwidth
          q hq hmem hfirst
      refine ⟨⟨0, by omega⟩, v, q v, hv, hqv, ?_, ?_, ?_⟩
      · simp
      · simpa only [Fin.val_zero, zero_mul, Nat.zero_mul, Nat.sub_zero]
          using hlow
      · intro hlt
        omega
  | succ steps ih =>
      let bandOne := (highBandMap (K := K) w Dlow delta T YS S).comp q
      let lowOne := LinearMap.ker bandOne
      have hrangeOne : Module.finrank K bandOne.range ≤
          delta * channelCount T YS S := by
        calc
          Module.finrank K bandOne.range ≤
              Module.finrank K (HighBandIndex delta T YS S → K) :=
            bandOne.range.finrank_le
          _ = delta * channelCount T YS S := by
            rw [Module.finrank_fintype_fun_eq_card, highBandIndex_card]
      have hlowOneRank :
          powerBandBudget delta
              (wt residualTotalWeights F) (wt residualYSWeights F)
              (wt residualSWeights F)
              (T - wt residualTotalWeights F)
              (YS - wt residualYSWeights F)
              (S - wt residualSWeights F) (steps + 1) <
            Module.finrank K lowOne := by
        have hsum := bandOne.finrank_range_add_finrank_ker
        change Module.finrank K bandOne.range + Module.finrank K lowOne =
          Module.finrank K V at hsum
        have hbudget :
            delta * channelCount T YS S +
                powerBandBudget delta
                  (wt residualTotalWeights F) (wt residualYSWeights F)
                  (wt residualSWeights F)
                  (T - wt residualTotalWeights F)
                  (YS - wt residualYSWeights F)
                  (S - wt residualSWeights F) (steps + 1) <
              Module.finrank K V := by
          simpa only [powerBandBudget, Nat.succ_eq_add_one,
            Nat.add_assoc] using hsource
        omega
      let qOne : lowOne →ₗ[K] P4 K := q.comp lowOne.subtype
      have hqOne : Function.Injective qOne := by
        intro a b hab
        apply Subtype.ext
        apply hq
        simpa only [qOne, LinearMap.comp_apply, Submodule.coe_subtype] using hab
      have hqOneBox : ∀ v : lowOne,
          qOne v ∈ nestedCoefficientBox K Dlow w T YS S := by
        intro v
        have hzero : highBandMap w Dlow delta T YS S (q v.1) = 0 := by
          have hv := v.2
          change bandOne v.1 = 0 at hv
          simpa only [bandOne, qOne, LinearMap.comp_apply,
            Submodule.coe_subtype] using hv
        simpa only [qOne, LinearMap.comp_apply, Submodule.coe_subtype] using
          mem_low_of_highBandMap_eq_zero Dhigh Dlow w delta T YS S hwidth
            (q v.1) (hmem v.1) hzero
      by_cases hdivOne : ∀ v : lowOne, F ∣ qOne v
      · let qTwo := quotientLinear qOne F hF hdivOne
        have hqTwo : Function.Injective qTwo :=
          quotientLinear_injective qOne hqOne F hF hdivOne
        have hqTwoBox : ∀ v : lowOne,
            qTwo v ∈ nestedCoefficientBox K
              (Dlow - wt (contactWeights w) F) w
              (T - wt residualTotalWeights F)
              (YS - wt residualYSWeights F)
              (S - wt residualSWeights F) := by
          intro v
          by_cases hv : v = 0
          · subst v
            rw [map_zero]
            exact (nestedCoefficientBox K _ _ _ _ _).zero_mem
          · have hqOneV : qOne v ≠ 0 := by
              intro hz
              apply hv
              apply hqOne
              simpa only [map_zero] using hz
            have hqTwoV : qTwo v ≠ 0 := by
              intro hz
              apply hqOneV
              rw [recon_eq_mul_quotientPolynomial qOne F hdivOne v]
              change F * qTwo v = 0
              rw [hz, mul_zero]
            exact quotient_mem_nestedCoefficientBox_of_mul_eq
              (qOne v) F (qTwo v) Dlow w T YS S hqOneV hF hqTwoV
                (hqOneBox v)
                (recon_eq_mul_quotientPolynomial qOne F hdivOne v)
        let DOneHigh := Dlow - wt (contactWeights w) F
        let DOneLow := Dlow - delta - wt (contactWeights w) F
        let TOne := T - wt residualTotalWeights F
        let YOne := YS - wt residualYSWeights F
        let SOne := S - wt residualSWeights F
        have hwidthRest : DOneHigh ≤ DOneLow + delta := by
          simp only [DOneHigh, DOneLow]
          omega
        obtain ⟨j, v, J, hv, hJ, heq, hbox, hterminal⟩ :=
          ih DOneHigh DOneLow TOne YOne SOne hwidthRest qTwo hqTwo
            (by simpa only [DOneHigh, TOne, YOne, SOne] using hqTwoBox)
            (by simpa only [TOne, YOne, SOne] using hlowOneRank)
        let jUp : Fin (Nat.succ steps + 1) := ⟨j.val + 1, by omega⟩
        refine ⟨jUp, v.1, J, ?_, hJ, ?_, ?_, ?_⟩
        · intro hz
          apply hv
          exact Subtype.ext hz
        · change F ^ (j.val + 1) * J = q v.1
          calc
            F ^ (j.val + 1) * J = F * (F ^ j.val * J) := by
              rw [pow_succ']
              ring
            _ = F * qTwo v := by rw [heq]
            _ = qOne v :=
              (recon_eq_mul_quotientPolynomial qOne F hdivOne v).symm
            _ = q v.1 := rfl
        · have hD :
              DOneLow - j.val * delta -
                  j.val * wt (contactWeights w) F =
                Dlow - (j.val + 1) * delta -
                  (j.val + 1) * wt (contactWeights w) F := by
              simp only [DOneLow, Nat.sub_sub, Nat.add_mul, one_mul]
              congr 1
              omega
          have hT : TOne - j.val * wt residualTotalWeights F =
              T - (j.val + 1) * wt residualTotalWeights F := by
            simp only [TOne, Nat.sub_sub, Nat.add_mul, one_mul]
            congr 1
            omega
          have hY : YOne - j.val * wt residualYSWeights F =
              YS - (j.val + 1) * wt residualYSWeights F := by
            simp only [YOne, Nat.sub_sub, Nat.add_mul, one_mul]
            congr 1
            omega
          have hS : SOne - j.val * wt residualSWeights F =
              S - (j.val + 1) * wt residualSWeights F := by
            simp only [SOne, Nat.sub_sub, Nat.add_mul, one_mul]
            congr 1
            omega
          simpa only [jUp, hD, hT, hY, hS] using hbox
        · intro hlt
          apply hterminal
          change j.val + 1 < steps + 1
          change j.val + 1 + 1 < Nat.succ steps + 1 at hlt
          omega
      · push Not at hdivOne
        obtain ⟨v, hvdiv⟩ := hdivOne
        have hv : v.1 ≠ 0 := by
          intro hz
          apply hvdiv
          have hvzero : v = 0 := Subtype.ext hz
          rw [hvzero]
          simp only [map_zero]
          exact dvd_zero F
        have hqv : q v.1 ≠ 0 := by
          intro hz
          apply hv
          apply hq
          simpa only [map_zero] using hz
        let jZero : Fin (Nat.succ steps + 1) := ⟨0, by omega⟩
        refine ⟨jZero, v.1, q v.1, hv, hqv, ?_, ?_, ?_⟩
        · simp only [jZero, Fin.val_zero, pow_zero, one_mul]
        · simpa only [jZero, Fin.val_zero, zero_mul, Nat.zero_mul,
            Nat.sub_zero, qOne, LinearMap.comp_apply, Submodule.coe_subtype]
            using hqOneBox v
        · intro _hlt
          simpa only [qOne, LinearMap.comp_apply, Submodule.coe_subtype]
            using hvdiv

end

end ProximityPrize.SubmissionLower.LocatorArbitraryPowerAvoidance
