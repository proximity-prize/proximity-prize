import ProximityPrize.SubmissionLower.Part.G001_00
section Compact_PackedLocatorTail
section PackedLocator_LocatorFifthPowerAvoidance
namespace ProximityPrize.SubmissionLower.LocatorFifthPowerAvoidance
open scoped BigOperators
open RCN081 RCN100 RCN119 RCN130 RCN156 RCN180 RCN234 RCN260
open LocatorLowQuotient LocatorCoprimeQuotient
open LocatorDoubleSquareAvoidance LocatorTripleCubeAvoidance
open LocatorFourthPowerAvoidance
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 1200000
variable {K V I : Type*} [Field K]
local instance : DecidableEq K := Classical.decEq K
section LinearDichotomy
variable [AddCommGroup V] [Module K V] [FiniteDimensional K V]



end LinearDichotomy

section FifthDerivative

variable [Fintype I]
local instance : DecidableEq I := Classical.decEq I



end FifthDerivative

end

end ProximityPrize.SubmissionLower.LocatorFifthPowerAvoidance
end PackedLocator_LocatorFifthPowerAvoidance

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorQuotientMonotone. -/
section PackedLocator_LocatorQuotientMonotone
namespace ProximityPrize.SubmissionLower.LocatorLowQuotient
open scoped BigOperators
theorem channelCount_mono {T T' YS YS' S S':ℕ}
    (ht:T ≤ T') (hy:YS ≤ YS') (hs:S ≤ S') :
    channelCount T YS S ≤ channelCount T' YS' S':=by
  rw [channelCount_eq, channelCount_eq]
  calc
    _ ≤ ∑ y ∈ Finset.range (min T YS + 1),
        ∑ r ∈ Finset.range (min S' (min (T' - y) (YS' - y)) + 1),
          (T' + 1 - y - r):=by
      apply Finset.sum_le_sum
      intro y _
      have hin:Finset.range (min S (min (T-y) (YS-y)) + 1) ⊆
          Finset.range (min S' (min (T'-y) (YS'-y)) + 1):=by
        apply Finset.range_mono
        have h:=min_le_min hs
          (min_le_min (Nat.sub_le_sub_right ht y) (Nat.sub_le_sub_right hy y))
        omega
      exact (Finset.sum_le_sum (fun r _ => by omega)).trans
        (Finset.sum_le_sum_of_subset_of_nonneg hin (fun _ _ _ => Nat.zero_le _))
    _ ≤ _:=by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · exact Finset.range_mono (Nat.add_le_add_right (min_le_min ht hy) 1)
      · intro _ _ _
        exact Nat.zero_le _
end ProximityPrize.SubmissionLower.LocatorLowQuotient
end PackedLocator_LocatorQuotientMonotone

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorArbitraryPowerAvoidance. -/
section PackedLocator_LocatorArbitraryPowerAvoidance

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


/-! ## Contact-thinned band (lever S1)

The band map reads coefficients at `highBandExponent w Dlow c`, `c : HighBandIndex`.  Every
monomial of the `Dhigh` box has `w * d1 + (w-1) * d2 ≤ Dhigh - 1` and `d2 ≤ S`, hence
`d1 + d2 ≤ (Dhigh + S - 1) / w`: index rows above that cut carry no monomial of the box, so
the band map built on the cut index set keeps its kernel inside the `Dlow` box, and its
rank bound is `delta * channelCount` of the cut caps.  The contact cap drops by
`delta + wt_c F` per level, so the cut sharpens with the depth. -/

/-- Largest `d 1 + d 2` a monomial of the `Dhigh` box (slope cap `S`) can have. -/
def thinTop (w Dhigh S : ℕ) : ℕ := (Dhigh + S - 1) / w

theorem thinTop_mono {w D D' S S' : ℕ} (hD : D ≤ D') (hS : S ≤ S') :
    thinTop w D S ≤ thinTop w D' S' :=
  Nat.div_le_div_right (by omega)

theorem ys_le_thinTop (Dhigh w T YS S : ℕ) (hw : 1 ≤ w) (d : Fin 4 →₀ ℕ)
    (hd : d ∈ nestedExponents Dhigh w T YS S) :
    d 1 + d 2 ≤ thinTop w Dhigh S := by
  rcases hd with ⟨_, _, hS, hD⟩
  have hwr : w * d 2 = (w - 1) * d 2 + d 2 := by
    calc
      w * d 2 = ((w - 1) + 1) * d 2 := by rw [Nat.sub_add_cancel hw]
      _ = (w - 1) * d 2 + d 2 := by ring
  have hmul : (d 1 + d 2) * w ≤ Dhigh + S - 1 := by
    rw [Nat.mul_comm, Nat.mul_add, hwr]
    omega
  exact (Nat.le_div_iff_mul_le (by omega)).mpr hmul

/-- `mem_low_of_highBandMap_eq_zero` for the band map built on the cut index set. -/
theorem mem_low_of_highBandMap_cut_eq_zero
    (Dhigh Dlow w delta T YS S : ℕ) (hw : 1 ≤ w)
    (hwidth : Dhigh ≤ Dlow + delta) (P : MvPolynomial (Fin 4) K)
    (hP : P ∈ nestedCoefficientBox K Dhigh w T YS S)
    (hzero : highBandMap w Dlow delta T (min YS (thinTop w Dhigh S)) S P = 0) :
    P ∈ nestedCoefficientBox K Dlow w T YS S := by
  intro d hd
  rcases hP hd with ⟨hT, hYS, hS, hD⟩
  have htop := ys_le_thinTop Dhigh w T YS S hw d ⟨hT, hYS, hS, hD⟩
  refine ⟨hT, hYS, hS, ?_⟩
  by_contra hnot
  have hy : d 1 < min T (min YS (thinTop w Dhigh S)) + 1 := by omega
  have hr : d 2 < min S (min (T - d 1) (min YS (thinTop w Dhigh S) - d 1)) + 1 := by
    omega
  have hz : d 3 < T + 1 - d 1 - d 2 := by omega
  have hstart : Dlow - w * d 1 - (w - 1) * d 2 ≤ d 0 := by omega
  have hx : d 0 - (Dlow - w * d 1 - (w - 1) * d 2) < delta := by omega
  let c : HighBandIndex delta T (min YS (thinTop w Dhigh S)) S :=
    ⟨⟨d 1, hy⟩, ⟨⟨d 2, hr⟩,
      ⟨⟨d 3, hz⟩, ⟨d 0 - (Dlow - w * d 1 - (w - 1) * d 2), hx⟩⟩⟩⟩
  have he : highBandExponent w Dlow c = d := by
    ext i
    fin_cases i <;> simp [highBandExponent, c] <;> omega
  have hc := congrFun hzero c
  have hcoeff : MvPolynomial.coeff d P = 0 := by
    simpa only [highBandMap_apply, he, Pi.zero_apply] using hc
  exact (MvPolynomial.mem_support_iff.mp hd) hcoeff

/-- The cell-side lower bound on the contact weight: the monomial attaining the
`YS` weight has slope exponent at most `wt_S F`. -/
theorem contact_ge_ys (w : ℕ) (hw : 1 ≤ w) (F : MvPolynomial (Fin 4) K) (hF : F ≠ 0) :
    w * wt residualYSWeights F - wt residualSWeights F ≤
      wt (contactWeights w) F := by
  obtain ⟨d, hd, hsup⟩ := Finset.exists_mem_eq_sup F.support
    (MvPolynomial.support_nonempty.mpr hF) (Finsupp.weight residualYSWeights)
  have hys : wt residualYSWeights F = d 1 + d 2 := by
    change MvPolynomial.weightedTotalDegree residualYSWeights F = d 1 + d 2
    rw [MvPolynomial.weightedTotalDegree, hsup, weight_fin4]
    simp [residualYSWeights]
  have hs : d 2 ≤ wt residualSWeights F := by
    have h := MvPolynomial.le_weightedTotalDegree residualSWeights hd
    rw [weight_fin4] at h
    change d 0 * 0 + d 1 * 0 + d 2 * 1 + d 3 * 0 ≤ wt residualSWeights F at h
    omega
  have hc : d 0 + w * d 1 + (w - 1) * d 2 ≤ wt (contactWeights w) F := by
    have h := MvPolynomial.le_weightedTotalDegree (contactWeights w) hd
    rw [contact_weight] at h
    exact h
  have hwr : w * d 2 = (w - 1) * d 2 + d 2 := by
    calc
      w * d 2 = ((w - 1) + 1) * d 2 := by rw [Nat.sub_add_cancel hw]
      _ = (w - 1) * d 2 + d 2 := by ring
  rw [hys, Nat.mul_add, hwr]
  omega

/-- The contact-aware budget: level `k+1` charges the cut band at contact cap `Dh` and
recurses with the cap lowered by `delta + dc` (`dc` a lower bound on `wt_c F`). -/
def powerBandBudgetThin
    (w Dh delta dc dT dY dS T YS S : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 =>
      delta * channelCount T (min YS (thinTop w Dh S)) S +
        powerBandBudgetThin w (Dh - delta - dc) delta dc dT dY dS
          (T - dT) (YS - dY) (S - dS) k

theorem powerBandBudgetThin_le (w delta dc dT dY dS : ℕ) :
    ∀ (k Dh T YS S : ℕ),
      powerBandBudgetThin w Dh delta dc dT dY dS T YS S k ≤
        powerBandBudget delta dT dY dS T YS S k := by
  intro k
  induction k with
  | zero => intro _ _ _ _; simp [powerBandBudgetThin, powerBandBudget]
  | succ k ih =>
      intro Dh T YS S
      simp only [powerBandBudgetThin, powerBandBudget]
      exact Nat.add_le_add
        (Nat.mul_le_mul_left delta
          (channelCount_mono le_rfl (Nat.min_le_left _ _) le_rfl))
        (ih _ _ _ _)

/-- Monotone: a larger cap, a smaller contact decrement, a larger box and smaller
per-stage losses can only increase the thin budget. -/
theorem powerBandBudgetThin_mono (w delta : ℕ) :
    ∀ (k Dh₁ dc₁ dT₁ dY₁ dS₁ T₁ Y₁ S₁ Dh₂ dc₂ dT₂ dY₂ dS₂ T₂ Y₂ S₂ : ℕ),
      Dh₁ ≤ Dh₂ → dc₂ ≤ dc₁ → T₁ ≤ T₂ → Y₁ ≤ Y₂ → S₁ ≤ S₂ →
      dT₂ ≤ dT₁ → dY₂ ≤ dY₁ → dS₂ ≤ dS₁ →
      powerBandBudgetThin w Dh₁ delta dc₁ dT₁ dY₁ dS₁ T₁ Y₁ S₁ k ≤
        powerBandBudgetThin w Dh₂ delta dc₂ dT₂ dY₂ dS₂ T₂ Y₂ S₂ k := by
  intro k
  induction k with
  | zero =>
      intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      simp [powerBandBudgetThin]
  | succ k ih =>
      intro Dh₁ dc₁ dT₁ dY₁ dS₁ T₁ Y₁ S₁ Dh₂ dc₂ dT₂ dY₂ dS₂ T₂ Y₂ S₂
        hD hdc hT hY hS hdT hdY hdS
      simp only [powerBandBudgetThin]
      apply Nat.add_le_add
      · exact Nat.mul_le_mul_left delta
          (channelCount_mono hT (min_le_min hY (thinTop_mono hD hS)) hS)
      · apply ih
        · omega
        · exact hdc
        · omega
        · omega
        · omega
        · exact hdT
        · exact hdY
        · exact hdS

theorem powerBandBudgetThin_le_succ
    (w Dh delta dc dT dY dS T YS S k : ℕ) :
    powerBandBudgetThin w Dh delta dc dT dY dS T YS S k ≤
      powerBandBudgetThin w Dh delta dc dT dY dS T YS S (k + 1) := by
  induction k generalizing Dh T YS S with
  | zero =>
      simp only [powerBandBudgetThin]
      exact Nat.zero_le _
  | succ k ih =>
      simp only [powerBandBudgetThin]
      exact Nat.add_le_add_left (ih _ _ _ _) _

theorem powerBandBudgetThin_mono_fuel
    (w Dh delta dc dT dY dS T YS S : ℕ) {k₁ k₂ : ℕ} (hk : k₁ ≤ k₂) :
    powerBandBudgetThin w Dh delta dc dT dY dS T YS S k₁ ≤
      powerBandBudgetThin w Dh delta dc dT dY dS T YS S k₂ := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hk
  induction d with
  | zero => simp
  | succ d ih =>
      calc
        powerBandBudgetThin w Dh delta dc dT dY dS T YS S k₁ ≤
            powerBandBudgetThin w Dh delta dc dT dY dS T YS S (k₁ + d) :=
          ih (Nat.le_add_right _ _)
        _ ≤ powerBandBudgetThin w Dh delta dc dT dY dS T YS S ((k₁ + d) + 1) :=
          powerBandBudgetThin_le_succ w Dh delta dc dT dY dS T YS S (k₁ + d)
        _ = powerBandBudgetThin w Dh delta dc dT dY dS T YS S (k₁ + d.succ) := by
          congr 1

end

end ProximityPrize.SubmissionLower.LocatorArbitraryPowerAvoidance
end PackedLocator_LocatorArbitraryPowerAvoidance

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorArbitraryPowerContact. -/
section PackedLocator_LocatorArbitraryPowerContact

/-!
# Arbitrary-order locator contact and power extraction

This module is the order-independent consumer for
`LocatorArbitraryPowerAvoidance`.  It replaces the explicitly unrolled
second-through-tenth derivative arguments by three reusable facts:

* an `R`-derivative lowers contact order by at most one;
* a nonzero `j`-fold `R`-derivative loses at least `j` times the `R` weight;
* at derivative order `j`, the surviving term of `dR^[j] (F^j * Q)` is
  `j! * Q * (dR F)^j` after specializing on `F = 0`.
-/

namespace ProximityPrize.SubmissionLower.LocatorArbitraryPowerContact

open scoped BigOperators
open RCN081 RCN100 RCN119 RCN130 RCN156 RCN180 RCN234 RCN260
open LocatorLowQuotient

noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

variable {K I : Type*} [Field K]
local instance : DecidableEq K := Classical.decEq K

abbrev P4 (K : Type*) [Field K] := MvPolynomial (Fin 4) K

/-- The `j`-fold derivative in the received-coordinate variable. -/
def iteratePderivR (j : ℕ) (Q : P4 K) : P4 K :=
  (fun H : P4 K => MvPolynomial.pderiv (2 : Fin 4) H)^[j] Q

@[simp] theorem iteratePderivR_zero (Q : P4 K) :
    iteratePderivR 0 Q = Q := rfl

theorem iteratePderivR_succ (j : ℕ) (Q : P4 K) :
    iteratePderivR (j + 1) Q =
      MvPolynomial.pderiv (2 : Fin 4) (iteratePderivR j Q) := by
  simp only [iteratePderivR, Function.iterate_succ_apply']

@[simp] theorem iteratePderivR_zero_poly (j : ℕ) :
    iteratePderivR (K := K) j 0 = 0 := by
  induction j with
  | zero => rfl
  | succ j ih =>
      rw [iteratePderivR_succ, ih, map_zero]

/-- Contact order falls by at most one at every received-coordinate
derivative, uniformly in the number of iterations. -/
theorem contactAtLeast_iteratePderivR
    (x u0 u1 : K) (m j : ℕ) (Q : P4 K)
    (hQ : ContactOrderBridge.ContactAtLeast K x u0 u1 m Q) :
    ContactOrderBridge.ContactAtLeast K x u0 u1 (m - j)
      (iteratePderivR j Q) := by
  induction j with
  | zero => simpa only [iteratePderivR_zero, Nat.sub_zero] using hQ
  | succ j ih =>
      rw [iteratePderivR_succ]
      have hnext := ContactOrderBridge.contactAtLeast_pderiv_R
        K x u0 u1 (m - j) (iteratePderivR j Q) ih
      simpa only [Nat.sub_sub] using hnext

/-- If a successor iterate is nonzero, its immediate predecessor is nonzero. -/
theorem iteratePderivR_ne_zero_of_succ
    (Q : P4 K) (j : ℕ)
    (hne : iteratePderivR (j + 1) Q ≠ 0) :
    iteratePderivR j Q ≠ 0 := by
  intro hz
  apply hne
  rw [iteratePderivR_succ, hz, map_zero]

/-- A nonzero `j`-fold received-coordinate derivative pays `j` copies of
the received-coordinate weight.  This is the generic replacement for all
manually chained `pderiv_R_weight_add_le` calculations. -/
theorem iteratePderivR_weight_add_le
    (weights : Fin 4 → ℕ) (Q : P4 K) (j : ℕ)
    (hne : iteratePderivR j Q ≠ 0) :
    wt weights (iteratePderivR j Q) + j * weights 2 ≤ wt weights Q := by
  induction j with
  | zero =>
      simp only [iteratePderivR_zero, Nat.zero_mul, Nat.add_zero]
      exact le_rfl
  | succ j ih =>
      have hprev : iteratePderivR j Q ≠ 0 :=
        iteratePderivR_ne_zero_of_succ Q j (by
          simpa only [Nat.succ_eq_add_one] using hne)
      have hstepNe :
          MvPolynomial.pderiv (2 : Fin 4) (iteratePderivR j Q) ≠ 0 := by
        simpa only [Nat.succ_eq_add_one, iteratePderivR_succ] using hne
      have hstep := LocatorContact.pderiv_R_weight_add_le
        weights (iteratePderivR j Q) hstepNe
      calc
        wt weights (iteratePderivR (Nat.succ j) Q) +
              Nat.succ j * weights 2 =
            (wt weights (MvPolynomial.pderiv (2 : Fin 4)
              (iteratePderivR j Q)) + weights 2) + j * weights 2 := by
              simp only [Nat.succ_eq_add_one, iteratePderivR_succ,
                Nat.add_mul, one_mul]
              ac_rfl
        _ ≤ wt weights (iteratePderivR j Q) + j * weights 2 :=
          Nat.add_le_add_right hstep _
        _ ≤ wt weights Q := ih hprev

theorem iteratePderivR_weight_le_sub
    (weights : Fin 4 → ℕ) (Q : P4 K) (j d : ℕ)
    (hne : iteratePderivR j Q ≠ 0)
    (hQ : wt weights Q ≤ d) :
    wt weights (iteratePderivR j Q) ≤ d - j * weights 2 := by
  exact Nat.le_sub_of_add_le
    ((iteratePderivR_weight_add_le weights Q j hne).trans hQ)

section KernelVanishing

variable [Fintype I]
local instance : DecidableEq I := Classical.decEq I

/-- The generic contact/degree vanishing theorem at derivative order `j`.
The capacity hypothesis is exactly the one used by each previously unrolled
fixed-order theorem. -/
theorem specialization_iteratePderivR_eq_zero_of_kernel_low_box
    (j D Dlow w L s m : ℕ) (nodes : I ↪ K) (u0 u1 : I → K)
    (v : ConstraintKernel (K := K) D w L s m nodes u0 u1)
    (hlow : reconstruct K D w L s v.1 ∈
      globalCoefficientBox K Dlow w L s)
    (P : Polynomial K) (gamma : K) (support : Finset I)
    (hj : 1 ≤ j) (hw : 1 ≤ w) (hP : P.natDegree ≤ w)
    (hcapacity : Dlow ≤ (m - j) * support.card + j * (w - 1))
    (hvalues : ∀ i ∈ support,
      P.eval (nodes i) = u0 i + gamma * u1 i) :
    RCN319.specialization K P gamma
      (iteratePderivR j (reconstruct K D w L s v.1)) = 0 := by
  classical
  cases j with
  | zero => omega
  | succ k =>
      let H := reconstruct K D w L s v.1
      by_contra hne
      have hfinal : iteratePderivR (Nat.succ k) H ≠ 0 := by
        intro hz
        apply hne
        rw [hz, map_zero]
      have hprev : iteratePderivR k H ≠ 0 := by
        apply iteratePderivR_ne_zero_of_succ H k
        simpa only [Nat.succ_eq_add_one] using hfinal
      have hH : H ≠ 0 := by
        intro hz
        apply hfinal
        rw [hz, iteratePderivR_zero_poly]
      have hDlow : 0 < Dlow := by
        obtain ⟨d, hd⟩ := MvPolynomial.support_nonempty.mpr hH
        have h := (hlow hd).2.2
        omega
      have hHweight : wt (contactWeights w) H ≤ Dlow - 1 :=
        ((mem_flagGlobalCoefficientBox_iff H Dlow w L s hDlow).mp hlow).2.2
      have hprevWeight :
          wt (contactWeights w) (iteratePderivR k H) ≤
            Dlow - 1 - k * (w - 1) := by
        have hbound := iteratePderivR_weight_le_sub
          (contactWeights w) H k (Dlow - 1) hprev hHweight
        change wt (contactWeights w) (iteratePderivR k H) ≤
          Dlow - 1 - k * (w - 1) at hbound
        exact hbound
      have hregular : RCN319.specialization K P gamma
          (MvPolynomial.pderiv (2 : Fin 4) (iteratePderivR k H)) ≠ 0 := by
        simpa only [Nat.succ_eq_add_one, iteratePderivR_succ] using hne
      have hdegree := ContactOrderBridge.specialized_R_derivative_degree K
        (iteratePderivR k H) P gamma w
        (Dlow - 1 - k * (w - 1)) hP hprevWeight hregular
      have hdegreeStrict :
          (RCN122.specialization K P gamma
            (iteratePderivR (Nat.succ k) H)).natDegree <
              (m - Nat.succ k) * support.card := by
        rw [Nat.succ_eq_add_one, iteratePderivR_succ]
        rw [RCN101.specialization_eq_ordinary]
        rw [RCN101.specialization_eq_ordinary] at hdegree
        have hkc : k * (w - 1) ≤ Dlow - 1 := by
          by_contra hnot
          have hlt : Dlow - 1 < k * (w - 1) := Nat.lt_of_not_ge hnot
          have hzero : Dlow - 1 - k * (w - 1) = 0 :=
            Nat.sub_eq_zero_of_le (Nat.le_of_lt hlt)
          rw [hzero] at hdegree
          have hwOne : w - 1 = 0 := by omega
          rw [hwOne, Nat.mul_zero] at hlt
          omega
        have hsplit :
            (Dlow - 1 - k * (w - 1)) + k * (w - 1) = Dlow - 1 :=
          Nat.sub_add_cancel hkc
        have hwSplit : w - 1 + 1 = w := Nat.sub_add_cancel hw
        simp only [Nat.succ_eq_add_one, Nat.add_mul, one_mul] at hcapacity
        omega
      have hcontact : ∀ i ∈ support, ∀ r : ℕ,
          slopeDifference K ^ (m - Nat.succ k - r) ∣
            (RCN122.homogenizedTranslation K (nodes i) (u0 i) (u1 i)
              (iteratePderivR (Nat.succ k) H)).coeff r := by
        intro i _hi
        apply (ContactOrderBridge.contactAtLeast_iff_block_divisibility
          K (nodes i) (u0 i) (u1 i) (m - Nat.succ k) _).mp
        exact contactAtLeast_iteratePderivR
          (nodes i) (u0 i) (u1 i) m (Nat.succ k) H
          (ContactOrderBridge.contactAtLeast_of_mem_kernel
            K D w L s m nodes u0 u1 v.1 v.2 i)
      have hz := RCN122.specialization_eq_zero_of_contact_and_degree K
        (iteratePderivR (Nat.succ k) H) P gamma nodes u0 u1 support
        (m - Nat.succ k) hcontact hvalues hdegreeStrict
      apply hne
      simpa only [H, RCN101.specialization_eq_ordinary] using hz

end KernelVanishing

/-- Local factorial divisibility criterion, kept here because `CH`'s
corresponding helper is intentionally private. -/
private theorem prime_dvd_factorial_local : ∀ {n p : ℕ},
    p.Prime → (p ∣ n.factorial ↔ p ≤ n)
  | 0, _, hp => iff_of_false hp.not_dvd_one (not_le_of_gt hp.pos)
  | n + 1, p, hp => by
      rw [Nat.factorial_succ, hp.dvd_mul, prime_dvd_factorial_local hp]
      exact ⟨fun h => h.elim (Nat.le_of_dvd (Nat.succ_pos _)) Nat.le_succ_of_le,
        fun h => (_root_.lt_or_eq_of_le h).elim
          (Or.inr ∘ Nat.le_of_lt_succ) fun h => Or.inl <| by rw [h]⟩

/-- A prime characteristic larger than `j` does not annihilate `j!`. -/
theorem factorial_ne_zero_of_lt_char
    (p j : ℕ) [CharP K p] (hp : p.Prime) (hj : j < p) :
    (j.factorial : K) ≠ 0 := by
  intro hz
  have hdvd : p ∣ j.factorial :=
    (CharP.cast_eq_zero_iff K p j.factorial).mp hz
  exact (not_le_of_gt hj) ((prime_dvd_factorial_local hp).mp hdvd)

/-- Generic extraction of the terminal quotient from a `j`th derivative.
After specializing on `F = 0`, `RCN324.iterate_pow_mul_expansion` kills its
error term and leaves `j! * Q * (dR F)^j`. -/
theorem specialization_eq_zero_of_iteratePderivR_power_product
    (j : ℕ) (P : Polynomial K) (gamma : K) (F Q : P4 K)
    (hfactorial : (j.factorial : K) ≠ 0)
    (hFzero : RCN319.specialization K P gamma F = 0)
    (hregular : RCN319.specialization K P gamma
      (MvPolynomial.pderiv (2 : Fin 4) F) ≠ 0)
    (hpower : RCN319.specialization K P gamma
      (iteratePderivR j (F ^ j * Q)) = 0) :
    RCN319.specialization K P gamma Q = 0 := by
  obtain ⟨error, herror⟩ := RCN324.iterate_pow_mul_expansion
    (MvPolynomial.pderiv (2 : Fin 4)) F Q j j le_rfl
  have hexpansion :
      iteratePderivR j (F ^ j * Q) =
        (j.descFactorial j : P4 K) * F ^ (j - j) * Q *
            (MvPolynomial.pderiv (2 : Fin 4) F) ^ j +
          F ^ (j - j + 1) * error := by
    simpa only [iteratePderivR] using herror
  rw [hexpansion] at hpower
  have hmul :
      (j.factorial : Polynomial K) *
          RCN319.specialization K P gamma Q *
            (RCN319.specialization K P gamma
              (MvPolynomial.pderiv (2 : Fin 4) F)) ^ j = 0 := by
    simpa only [Nat.descFactorial_self, Nat.sub_self, pow_zero, one_mul, mul_one,
      zero_add, pow_one, map_add, map_mul, map_pow, map_natCast,
      map_one, hFzero, zero_mul, add_zero] using hpower
  have hfactorialPoly : (j.factorial : Polynomial K) ≠ 0 := by
    intro hz
    apply hfactorial
    have heval := congrArg (Polynomial.eval 0) hz
    simpa using heval
  have hcoef :
      (j.factorial : Polynomial K) *
          (RCN319.specialization K P gamma
            (MvPolynomial.pderiv (2 : Fin 4) F)) ^ j ≠ 0 :=
    mul_ne_zero hfactorialPoly (pow_ne_zero j hregular)
  have hmul' :
      ((j.factorial : Polynomial K) *
          (RCN319.specialization K P gamma
            (MvPolynomial.pderiv (2 : Fin 4) F)) ^ j) *
        RCN319.specialization K P gamma Q = 0 := by
    calc
      _ = (j.factorial : Polynomial K) *
          RCN319.specialization K P gamma Q *
            (RCN319.specialization K P gamma
              (MvPolynomial.pderiv (2 : Fin 4) F)) ^ j := by ring
      _ = 0 := hmul
  exact (mul_eq_zero.mp hmul').resolve_left hcoef

end

end ProximityPrize.SubmissionLower.LocatorArbitraryPowerContact
end PackedLocator_LocatorArbitraryPowerContact

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorTwoFactorAvoidance. -/
section PackedLocator_LocatorTwoFactorAvoidance

/-!
# A shared high-band route for two regular factors

The one-factor power route pays for a high-band projection independently for
every regular factor.  For two factors the projection can be shared.  On the
resulting low subspace there are only four cases: neither divisibility
condition is universal, exactly one is universal, or both are universal.  In
the first case one vector avoids both divisors; in a one-universal case the
other factor is finished and the universal factor continues through the
one-factor route; in the both-universal case the product is divided out and
the shared route continues.

This file contains the linear-algebraic core.  It intentionally returns
weight bounds rather than coefficient-box membership: those are precisely
the data consumed by the derivative and unequal-pair arguments, and they are
stable when the other factor is multiplied back into a recursively produced
helper.
-/

namespace ProximityPrize.SubmissionLower.LocatorTwoFactorAvoidance

open scoped BigOperators
open UniqueFactorizationMonoid
open RCN081 RCN100 RCN119 RCN130 RCN140 RCN156 RCN180 RCN234 RCN260
open LocatorLowQuotient LocatorCoprimeQuotient
  LocatorDoubleSquareAvoidance LocatorArbitraryPowerAvoidance
  LocatorArbitraryPowerContact

noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

variable {K V : Type} [Field K]
local instance : DecidableEq K := Classical.decEq K
local instance : StrongNormalizationMonoid (MvPolynomial (Fin 4) K) :=
  UniqueFactorizationMonoid.strongNormalizationMonoid

abbrev P4 (K : Type*) [Field K] := MvPolynomial (Fin 4) K

/-- The budget for a shared two-factor route.  After the current common band
there are three possible continuations: only `F`, only `G`, or both.  Taking
their maximum is sound because the divisibility case split chooses only one
continuation. -/
def twoFactorBandBudget
    (delta fT fY fS gT gY gS T YS S : ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 =>
      delta * channelCount T YS S +
        max
          (powerBandBudget delta fT fY fS
            (T - fT) (YS - fY) (S - fS) n)
          (max
            (powerBandBudget delta gT gY gS
              (T - gT) (YS - gY) (S - gS) n)
            (twoFactorBandBudget delta fT fY fS gT gY gS
              (T - fT - gT) (YS - fY - gY) (S - fS - gS) n))

/-- A stage for one target factor.  `j` records how many copies have been
removed from the input family.  At a nonterminal stage the helper is coprime
to the target irreducible; at the last stage the consumer may instead use a
terminal weight inequality. -/
def HasFactorStage [AddCommMonoid V] [Module K V]
    (fuel Dlow w delta T YS S : ℕ)
    (q : V →ₗ[K] P4 K) (F : P4 K) : Prop :=
  ∃ (j : Fin fuel) (v : V) (J : P4 K),
    v ≠ 0 ∧ J ≠ 0 ∧ F ^ j.val * J = q v ∧
    wt residualTotalWeights J ≤ T - j.val * wt residualTotalWeights F ∧
    wt residualYSWeights J ≤ YS - j.val * wt residualYSWeights F ∧
    wt residualSWeights J ≤ S - j.val * wt residualSWeights F ∧
    wt (contactWeights w) J <
      Dlow - j.val * delta - j.val * wt (contactWeights w) F ∧
    (j.val + 1 < fuel → ¬ F ∣ J)

/-- Two proper divisibility subspaces cannot cover a vector space.  For two
subspaces this has a particularly cheap constructive proof: in the crossed
case `x + y` avoids both divisors. -/
theorem exists_not_dvd_both
    [AddCommGroup V] [Module K V]
    (q : V →ₗ[K] P4 K) (F G : P4 K)
    (hF : ¬ ∀ v, F ∣ q v) (hG : ¬ ∀ v, G ∣ q v) :
    ∃ v, ¬ F ∣ q v ∧ ¬ G ∣ q v := by
  classical
  push_neg at hF hG
  obtain ⟨x, hxF⟩ := hF
  obtain ⟨y, hyG⟩ := hG
  by_cases hxG : G ∣ q x
  · by_cases hyF : F ∣ q y
    · refine ⟨x + y, ?_, ?_⟩
      · intro hsum
        apply hxF
        have hd : F ∣ q (x + y) - q y := dvd_sub hsum hyF
        simpa only [map_add, add_sub_cancel_right] using hd
      · intro hsum
        apply hyG
        have hd : G ∣ q (x + y) - q x := dvd_sub hsum hxG
        simpa only [map_add, add_sub_cancel_left] using hd
    · exact ⟨y, hyF, hyG⟩
  · exact ⟨x, hxF, hxG⟩

/-- Package the four cases used by the shared recursion. -/
theorem two_divisor_cases
    [AddCommGroup V] [Module K V]
    (q : V →ₗ[K] P4 K) (F G : P4 K) :
    ((∀ v, F ∣ q v) ∧ (∀ v, G ∣ q v)) ∨
      ((∀ v, F ∣ q v) ∧ ∃ v, ¬ G ∣ q v) ∨
      ((∃ v, ¬ F ∣ q v) ∧ ∀ v, G ∣ q v) ∨
      ∃ v, ¬ F ∣ q v ∧ ¬ G ∣ q v := by
  classical
  by_cases hF : ∀ v, F ∣ q v
  · by_cases hG : ∀ v, G ∣ q v
    · exact Or.inl ⟨hF, hG⟩
    · right; left
      push_neg at hG
      exact ⟨hF, hG⟩
  · by_cases hG : ∀ v, G ∣ q v
    · right; right; left
      push_neg at hF
      exact ⟨hF, hG⟩
    · right; right; right
      exact exists_not_dvd_both q F G hF hG

private theorem regular_mem_normalizedFactors
    (H : P4 K) (F : RCN266.RegularIndex H) :
    F.1 ∈ normalizedFactors H := by
  have hactive : F.1 ∈ RCN082.activeFactors H :=
    (Finset.mem_filter.mp F.2).1
  have hnf : F.1 ∈ (normalizedFactors H).toFinset :=
    (Finset.mem_filter.mp hactive).1
  exact Multiset.mem_toFinset.mp hnf

/-- Distinct regular indices are represented by distinct normalized prime
factors, hence are relatively prime. -/
theorem regularIndex_isRelPrime_of_ne
    (H : P4 K) (F G : RCN266.RegularIndex H) (hne : F.1 ≠ G.1) :
    IsRelPrime F.1 G.1 := by
  have hFs := RCN167.positiveRFactors_spec H F.1 F.2
  have hGs := RCN167.positiveRFactors_spec H G.1 G.2
  apply hFs.1.isRelPrime_iff_not_dvd.mpr
  intro hd
  apply hne
  apply UniqueFactorizationMonoid.mem_normalizedFactors_eq_of_associated
    (regular_mem_normalizedFactors H F) (regular_mem_normalizedFactors H G)
  exact (hFs.1.dvd_irreducible_iff_associated hGs.1).mp hd


/-- Dividing an injective nested-box family by a universal divisor preserves
injectivity and subtracts the four factor weights. -/
theorem quotientLinear_nested_data
    [AddCommGroup V] [Module K V]
    (D w T YS S : ℕ) (q : V →ₗ[K] P4 K)
    (hq : Function.Injective q)
    (hmem : ∀ v, q v ∈ nestedCoefficientBox K D w T YS S)
    (F : P4 K) (hF : F ≠ 0) (hdiv : ∀ v, F ∣ q v) :
    Function.Injective (quotientLinear q F hF hdiv) ∧
      (∀ v, q v = F * quotientLinear q F hF hdiv v) ∧
      ∀ v, quotientLinear q F hF hdiv v ∈ nestedCoefficientBox K
        (D - wt (contactWeights w) F) w
        (T - wt residualTotalWeights F)
        (YS - wt residualYSWeights F)
        (S - wt residualSWeights F) := by
  classical
  let qF := quotientLinear q F hF hdiv
  have hqF : Function.Injective qF :=
    quotientLinear_injective q hq F hF hdiv
  have hprod (v : V) : q v = F * qF v :=
    recon_eq_mul_quotientPolynomial q F hdiv v
  refine ⟨hqF, hprod, ?_⟩
  intro v
  by_cases hv : v = 0
  · subst v
    rw [map_zero]
    exact (nestedCoefficientBox K _ _ _ _ _).zero_mem
  · have hqv : q v ≠ 0 := by
      intro hz
      apply hv
      apply hq
      simpa only [map_zero] using hz
    have hqFv : qF v ≠ 0 := by
      intro hz
      apply hqv
      rw [hprod v, hz, mul_zero]
    exact quotient_mem_nestedCoefficientBox_of_mul_eq
      (q v) F (qF v) D w T YS S hqv hF hqFv (hmem v) (hprod v)

/-- Quotient an `FG`-divisible source family by both factors while retaining
the separated weight decrements needed by the pair budget. -/
theorem exists_twoFactor_quotient_nested_data
    [AddCommGroup V] [Module K V]
    (D w T YS S : ℕ) (q : V →ₗ[K] P4 K)
    (hq : Function.Injective q)
    (hmem : ∀ v, q v ∈ nestedCoefficientBox K D w T YS S)
    (F G : P4 K) (hF : F ≠ 0) (hG : G ≠ 0)
    (hrel : IsRelPrime F G)
    (hdivF : ∀ v, F ∣ q v) (hdivG : ∀ v, G ∣ q v) :
    ∃ qFG : V →ₗ[K] P4 K,
      Function.Injective qFG ∧
      (∀ v, q v = F * (G * qFG v)) ∧
      ∀ v, qFG v ∈ nestedCoefficientBox K
        (D - wt (contactWeights w) F - wt (contactWeights w) G) w
        (T - wt residualTotalWeights F - wt residualTotalWeights G)
        (YS - wt residualYSWeights F - wt residualYSWeights G)
        (S - wt residualSWeights F - wt residualSWeights G) := by
  let qF := quotientLinear q F hF hdivF
  have hdataF := quotientLinear_nested_data D w T YS S q hq hmem F hF hdivF
  have hqF : Function.Injective qF := by
    simpa only [qF] using hdataF.1
  have hprodF : ∀ v, q v = F * qF v := by
    simpa only [qF] using hdataF.2.1
  have hqFBox : ∀ v, qF v ∈ nestedCoefficientBox K
      (D - wt (contactWeights w) F) w
      (T - wt residualTotalWeights F)
      (YS - wt residualYSWeights F)
      (S - wt residualSWeights F) := by
    simpa only [qF] using hdataF.2.2
  have hdivG' : ∀ v, G ∣ qF v := by
    intro v
    apply hrel.symm.dvd_of_dvd_mul_left
    rw [← hprodF v]
    exact hdivG v
  let qFG := quotientLinear qF G hG hdivG'
  have hdataG := quotientLinear_nested_data
    (D - wt (contactWeights w) F) w
    (T - wt residualTotalWeights F)
    (YS - wt residualYSWeights F)
    (S - wt residualSWeights F)
    qF hqF hqFBox G hG hdivG'
  refine ⟨qFG, ?_, ?_, ?_⟩
  · simpa only [qFG] using hdataG.1
  · intro v
    calc
      q v = F * qF v := hprodF v
      _ = F * (G * qFG v) := by
        rw [hdataG.2.1 v]
  · simpa only [qFG] using hdataG.2.2

/-- Exact weighted degree of a nonzero power. -/
theorem wt_pow_eq (weights : Fin 4 → ℕ) (F : P4 K) (hF : F ≠ 0)
    (j : ℕ) : wt weights (F ^ j) = j * wt weights F := by
  unfold wt
  induction j with
  | zero => simp [pow_zero, MvPolynomial.weightedTotalDegree]
  | succ j ih =>
      rw [pow_succ', weightedTotalDegree_mul weights F (F ^ j) hF
        (pow_ne_zero j hF), ih]
      simp only [Nat.succ_eq_add_one, Nat.add_mul, one_mul]
      omega

/-- If a boxed polynomial is `F^j * J`, the three residual weights of `J`
are the ambient weights minus the corresponding factor weights. -/
theorem residual_bounds_of_power_identity
    (D w T YS S j : ℕ) (P F J : P4 K)
    (hP : P ≠ 0) (hF : F ≠ 0) (hJ : J ≠ 0)
    (hbox : P ∈ nestedCoefficientBox K D w T YS S)
    (heq : F ^ j * J = P) :
    wt residualTotalWeights J ≤ T - j * wt residualTotalWeights F ∧
      wt residualYSWeights J ≤ YS - j * wt residualYSWeights F ∧
      wt residualSWeights J ≤ S - j * wt residualSWeights F := by
  have hb := nested_mem_weights hbox hP
  have one (weights : Fin 4 → ℕ) (B : ℕ)
      (hPB : wt weights P ≤ B) :
      wt weights J ≤ B - j * wt weights F := by
    have hm := weightedTotalDegree_mul weights (F ^ j) J
      (pow_ne_zero j hF) hJ
    have hp := wt_pow_eq weights F hF j
    unfold wt at hPB ⊢ hp
    rw [hp, heq] at hm
    omega
  exact ⟨one residualTotalWeights T hb.1,
    one residualYSWeights YS hb.2.1,
    one residualSWeights S hb.2.2.1⟩

private theorem sub_one_then_mul (a b j : ℕ) :
    a - b - j * b = a - (j + 1) * b := by
  simp only [Nat.sub_sub, Nat.add_mul, one_mul]
  congr 1
  omega

private theorem sub_pair_then_mul (a x y j : ℕ) :
    a - x - y - j * x - j * y =
      a - (j + 1) * x - (j + 1) * y := by
  simp only [Nat.sub_sub, Nat.add_mul, one_mul]
  congr 1
  omega

/-- Arithmetic used when a recursively produced helper for one factor is
multiplied by the other factor.  Expanding `(j+1) * _` first keeps the proof
inside Presburger arithmetic. -/
private theorem cross_contact_lt
    (a delta cSelf cOther j x : ℕ)
    (h : x < a - delta - cSelf - cOther - j * delta - j * cSelf) :
    cOther + x < a - (j + 1) * delta - (j + 1) * cSelf := by
  simp only [Nat.add_mul, one_mul]
  omega

/-- A single high-band chain simultaneously supplies helpers for two coprime
factors.  Relative to two independent invocations, the first band is always
paid once; whenever both divisibility conditions remain universal, all later
bands are shared as well. -/
theorem exists_two_factor_stages_of_bandBudget_succ
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (steps Dhigh Dlow w delta T YS S : ℕ)
    (hwidth : Dhigh ≤ Dlow + delta)
    (q : V →ₗ[K] P4 K) (hq : Function.Injective q)
    (hmem : ∀ v, q v ∈ nestedCoefficientBox K Dhigh w T YS S)
    (F G : P4 K) (hF : F ≠ 0) (hG : G ≠ 0)
    (hrel : IsRelPrime F G)
    (hsource :
      twoFactorBandBudget delta
          (wt residualTotalWeights F) (wt residualYSWeights F)
          (wt residualSWeights F)
          (wt residualTotalWeights G) (wt residualYSWeights G)
          (wt residualSWeights G) T YS S (steps + 1) <
        Module.finrank K V) :
    HasFactorStage (steps + 1) Dlow w delta T YS S q F ∧
      HasFactorStage (steps + 1) Dlow w delta T YS S q G := by
  classical
  induction steps generalizing V Dhigh Dlow T YS S with
  | zero =>
      have hfirst : delta * channelCount T YS S < Module.finrank K V := by
        simpa [twoFactorBandBudget, powerBandBudget] using hsource
      obtain ⟨v, hv, hqv, hlow⟩ :=
        exists_nonzero_image_mem_low Dhigh Dlow w delta T YS S hwidth
          q hq hmem hfirst
      have hb := nested_mem_weights hlow hqv
      let j0 : Fin (0 + 1) := ⟨0, by omega⟩
      have one (A : P4 K) :
          HasFactorStage (0 + 1) Dlow w delta T YS S q A := by
        refine ⟨j0, v, q v, hv, hqv, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · simp only [j0, Fin.val_zero, pow_zero, one_mul]
        · simpa only [j0, Fin.val_zero, zero_mul, Nat.sub_zero] using hb.1
        · simpa only [j0, Fin.val_zero, zero_mul, Nat.sub_zero] using hb.2.1
        · simpa only [j0, Fin.val_zero, zero_mul, Nat.sub_zero] using hb.2.2.1
        · simpa only [j0, Fin.val_zero, zero_mul, Nat.sub_zero] using hb.2.2.2
        · intro hlt
          omega
      exact ⟨one F, one G⟩
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
      have htail :
          max
            (powerBandBudget delta
              (wt residualTotalWeights F) (wt residualYSWeights F)
              (wt residualSWeights F)
              (T - wt residualTotalWeights F)
              (YS - wt residualYSWeights F)
              (S - wt residualSWeights F) (steps + 1))
            (max
              (powerBandBudget delta
                (wt residualTotalWeights G) (wt residualYSWeights G)
                (wt residualSWeights G)
                (T - wt residualTotalWeights G)
                (YS - wt residualYSWeights G)
                (S - wt residualSWeights G) (steps + 1))
              (twoFactorBandBudget delta
                (wt residualTotalWeights F) (wt residualYSWeights F)
                (wt residualSWeights F)
                (wt residualTotalWeights G) (wt residualYSWeights G)
                (wt residualSWeights G)
                (T - wt residualTotalWeights F - wt residualTotalWeights G)
                (YS - wt residualYSWeights F - wt residualYSWeights G)
                (S - wt residualSWeights F - wt residualSWeights G)
                (steps + 1))) < Module.finrank K lowOne := by
        have hsum := bandOne.finrank_range_add_finrank_ker
        change Module.finrank K bandOne.range + Module.finrank K lowOne =
          Module.finrank K V at hsum
        have hbudget := hsource
        rw [twoFactorBandBudget] at hbudget
        have hrangeTail : Module.finrank K bandOne.range +
            max
              (powerBandBudget delta
                (wt residualTotalWeights F) (wt residualYSWeights F)
                (wt residualSWeights F)
                (T - wt residualTotalWeights F)
                (YS - wt residualYSWeights F)
                (S - wt residualSWeights F) (steps + 1))
              (max
                (powerBandBudget delta
                  (wt residualTotalWeights G) (wt residualYSWeights G)
                  (wt residualSWeights G)
                  (T - wt residualTotalWeights G)
                  (YS - wt residualYSWeights G)
                  (S - wt residualSWeights G) (steps + 1))
                (twoFactorBandBudget delta
                  (wt residualTotalWeights F) (wt residualYSWeights F)
                  (wt residualSWeights F)
                  (wt residualTotalWeights G) (wt residualYSWeights G)
                  (wt residualSWeights G)
                  (T - wt residualTotalWeights F - wt residualTotalWeights G)
                  (YS - wt residualYSWeights F - wt residualYSWeights G)
                  (S - wt residualSWeights F - wt residualSWeights G)
                  (steps + 1))) < Module.finrank K V := by
          exact (Nat.add_le_add_right hrangeOne _).trans_lt (by
            simpa only [Nat.succ_eq_add_one] using hbudget)
        rw [← hsum] at hrangeTail
        exact Nat.lt_of_add_lt_add_left hrangeTail
      have hsourceF :
          powerBandBudget delta
              (wt residualTotalWeights F) (wt residualYSWeights F)
              (wt residualSWeights F)
              (T - wt residualTotalWeights F)
              (YS - wt residualYSWeights F)
              (S - wt residualSWeights F) (steps + 1) <
            Module.finrank K lowOne :=
        (Nat.le_max_left _ _).trans_lt htail
      have hsourceG :
          powerBandBudget delta
              (wt residualTotalWeights G) (wt residualYSWeights G)
              (wt residualSWeights G)
              (T - wt residualTotalWeights G)
              (YS - wt residualYSWeights G)
              (S - wt residualSWeights G) (steps + 1) <
            Module.finrank K lowOne :=
        ((Nat.le_max_left _ _).trans (Nat.le_max_right _ _)).trans_lt htail
      have hsourceBoth :
          twoFactorBandBudget delta
              (wt residualTotalWeights F) (wt residualYSWeights F)
              (wt residualSWeights F)
              (wt residualTotalWeights G) (wt residualYSWeights G)
              (wt residualSWeights G)
              (T - wt residualTotalWeights F - wt residualTotalWeights G)
              (YS - wt residualYSWeights F - wt residualYSWeights G)
              (S - wt residualSWeights F - wt residualSWeights G)
              (steps + 1) < Module.finrank K lowOne :=
        ((Nat.le_max_right _ _).trans (Nat.le_max_right _ _)).trans_lt htail
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
      have immediate (A : P4 K) (v : lowOne) (hnot : ¬ A ∣ qOne v) :
          HasFactorStage (Nat.succ steps + 1) Dlow w delta T YS S q A := by
        have hv : v.1 ≠ 0 := by
          intro hz
          apply hnot
          have hvzero : v = 0 := Subtype.ext hz
          rw [hvzero]
          simp only [map_zero]
          exact dvd_zero A
        have hqv : qOne v ≠ 0 := by
          intro hz
          apply hv
          apply hq
          simpa only [qOne, LinearMap.comp_apply, Submodule.coe_subtype,
            map_zero] using hz
        have hb := nested_mem_weights (hqOneBox v) hqv
        let j0 : Fin (Nat.succ steps + 1) := ⟨0, by omega⟩
        refine ⟨j0, v.1, qOne v, hv, hqv, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · simp only [j0, Fin.val_zero, pow_zero, one_mul, qOne,
            LinearMap.comp_apply, Submodule.coe_subtype]
        · simpa only [j0, Fin.val_zero, zero_mul, Nat.sub_zero] using hb.1
        · simpa only [j0, Fin.val_zero, zero_mul, Nat.sub_zero] using hb.2.1
        · simpa only [j0, Fin.val_zero, zero_mul, Nat.sub_zero] using hb.2.2.1
        · simpa only [j0, Fin.val_zero, zero_mul, Nat.sub_zero] using hb.2.2.2
        · intro _hlt
          exact hnot
      rcases two_divisor_cases qOne F G with hboth | honeF | honeG | hneither
      · rcases hboth with ⟨hdivF, hdivG⟩
        let qF := quotientLinear qOne F hF hdivF
        have hdataF := quotientLinear_nested_data Dlow w T YS S qOne hqOne
          hqOneBox F hF hdivF
        have hqF : Function.Injective qF := by
          simpa only [qF] using hdataF.1
        have hprodF : ∀ v, qOne v = F * qF v := by
          simpa only [qF] using hdataF.2.1
        have hqFBox : ∀ v, qF v ∈ nestedCoefficientBox K
            (Dlow - wt (contactWeights w) F) w
            (T - wt residualTotalWeights F)
            (YS - wt residualYSWeights F)
            (S - wt residualSWeights F) := by
          simpa only [qF] using hdataF.2.2
        have hdivG' : ∀ v, G ∣ qF v := by
          intro v
          apply hrel.symm.dvd_of_dvd_mul_left
          rw [← hprodF v]
          exact hdivG v
        let qFG := quotientLinear qF G hG hdivG'
        have hdataG := quotientLinear_nested_data
          (Dlow - wt (contactWeights w) F) w
          (T - wt residualTotalWeights F)
          (YS - wt residualYSWeights F)
          (S - wt residualSWeights F)
          qF hqF hqFBox G hG hdivG'
        have hqFG : Function.Injective qFG := by
          simpa only [qFG] using hdataG.1
        have hprodG : ∀ v, qF v = G * qFG v := by
          simpa only [qFG] using hdataG.2.1
        have hqFGBox : ∀ v, qFG v ∈ nestedCoefficientBox K
            (Dlow - wt (contactWeights w) F - wt (contactWeights w) G) w
            (T - wt residualTotalWeights F - wt residualTotalWeights G)
            (YS - wt residualYSWeights F - wt residualYSWeights G)
            (S - wt residualSWeights F - wt residualSWeights G) := by
          simpa only [qFG] using hdataG.2.2
        have hwidthRest :
            Dlow - wt (contactWeights w) F - wt (contactWeights w) G ≤
              (Dlow - delta - wt (contactWeights w) F -
                wt (contactWeights w) G) + delta := by
          omega
        obtain ⟨stageF, stageG⟩ := ih
          (Dlow - wt (contactWeights w) F - wt (contactWeights w) G)
          (Dlow - delta - wt (contactWeights w) F -
            wt (contactWeights w) G)
          (T - wt residualTotalWeights F - wt residualTotalWeights G)
          (YS - wt residualYSWeights F - wt residualYSWeights G)
          (S - wt residualSWeights F - wt residualSWeights G)
          hwidthRest qFG hqFG hqFGBox hsourceBoth
        have liftF :
            HasFactorStage (Nat.succ steps + 1) Dlow w delta T YS S q F := by
          rcases stageF with
            ⟨j, v, J, hv, hJ, heq, _hT, _hY, _hS, hC, hterminal⟩
          let jUp : Fin (Nat.succ steps + 1) := ⟨j.val + 1, by omega⟩
          let JUp := G * J
          have hJUp : JUp ≠ 0 := mul_ne_zero hG hJ
          have hv' : v.1 ≠ 0 := by
            intro hz
            apply hv
            exact Subtype.ext hz
          have heqOne : F ^ (j.val + 1) * JUp = qOne v := by
            calc
              F ^ (j.val + 1) * JUp = F * (G * (F ^ j.val * J)) := by
                simp only [JUp, pow_succ']
                ring
              _ = F * (G * qFG v) := by rw [heq]
              _ = F * qF v := by rw [← hprodG v]
              _ = qOne v := (hprodF v).symm
          have hqOneV : qOne v ≠ 0 := by
            intro hz
            apply hv
            apply hqOne
            simpa only [map_zero] using hz
          have hb := residual_bounds_of_power_identity Dlow w T YS S
            (j.val + 1) (qOne v) F JUp hqOneV hF hJUp
            (hqOneBox v) heqOne
          refine ⟨jUp, v.1, JUp, hv', hJUp, ?_, hb.1, hb.2.1,
            hb.2.2, ?_, ?_⟩
          · simpa only [jUp, qOne, LinearMap.comp_apply,
              Submodule.coe_subtype] using heqOne
          · have hm : wt (contactWeights w) JUp ≤
                wt (contactWeights w) G + wt (contactWeights w) J := by
              simpa only [JUp] using wt_mul_le (contactWeights w) G J
            exact hm.trans_lt (by
              simpa only [jUp] using cross_contact_lt Dlow delta
                (wt (contactWeights w) F) (wt (contactWeights w) G)
                j.val (wt (contactWeights w) J) hC)
          · intro hlt
            have hn : ¬ F ∣ J := by
              apply hterminal
              change j.val + 1 < steps + 1
              change j.val + 1 + 1 < Nat.succ steps + 1 at hlt
              omega
            intro hd
            exact hn (hrel.dvd_of_dvd_mul_left hd)
        have liftG :
            HasFactorStage (Nat.succ steps + 1) Dlow w delta T YS S q G := by
          rcases stageG with
            ⟨j, v, J, hv, hJ, heq, _hT, _hY, _hS, hC, hterminal⟩
          let jUp : Fin (Nat.succ steps + 1) := ⟨j.val + 1, by omega⟩
          let JUp := F * J
          have hJUp : JUp ≠ 0 := mul_ne_zero hF hJ
          have hv' : v.1 ≠ 0 := by
            intro hz
            apply hv
            exact Subtype.ext hz
          have heqOne : G ^ (j.val + 1) * JUp = qOne v := by
            calc
              G ^ (j.val + 1) * JUp = F * (G * (G ^ j.val * J)) := by
                simp only [JUp, pow_succ']
                ring
              _ = F * (G * qFG v) := by rw [heq]
              _ = F * qF v := by rw [← hprodG v]
              _ = qOne v := (hprodF v).symm
          have hqOneV : qOne v ≠ 0 := by
            intro hz
            apply hv
            apply hqOne
            simpa only [map_zero] using hz
          have hb := residual_bounds_of_power_identity Dlow w T YS S
            (j.val + 1) (qOne v) G JUp hqOneV hG hJUp
            (hqOneBox v) heqOne
          refine ⟨jUp, v.1, JUp, hv', hJUp, ?_, hb.1, hb.2.1,
            hb.2.2, ?_, ?_⟩
          · simpa only [jUp, qOne, LinearMap.comp_apply,
              Submodule.coe_subtype] using heqOne
          · have hm : wt (contactWeights w) JUp ≤
                wt (contactWeights w) F + wt (contactWeights w) J := by
              simpa only [JUp] using wt_mul_le (contactWeights w) F J
            have hC' : wt (contactWeights w) J <
                Dlow - delta - wt (contactWeights w) G -
                  wt (contactWeights w) F - j.val * delta -
                    j.val * wt (contactWeights w) G := by
              simpa only [Nat.sub_sub, Nat.add_comm, Nat.add_left_comm,
                Nat.add_assoc] using hC
            exact hm.trans_lt (by
              simpa only [jUp] using cross_contact_lt Dlow delta
                (wt (contactWeights w) G) (wt (contactWeights w) F)
                j.val (wt (contactWeights w) J) hC')
          · intro hlt
            have hn : ¬ G ∣ J := by
              apply hterminal
              change j.val + 1 < steps + 1
              change j.val + 1 + 1 < Nat.succ steps + 1 at hlt
              omega
            intro hd
            exact hn (hrel.symm.dvd_of_dvd_mul_left hd)
        exact ⟨liftF, liftG⟩
      · rcases honeF with ⟨hdivF, ⟨vG, hvG⟩⟩
        let qF := quotientLinear qOne F hF hdivF
        have hdataF := quotientLinear_nested_data Dlow w T YS S qOne hqOne
          hqOneBox F hF hdivF
        have hqF : Function.Injective qF := by
          simpa only [qF] using hdataF.1
        have hprodF : ∀ v, qOne v = F * qF v := by
          simpa only [qF] using hdataF.2.1
        have hqFBox : ∀ v, qF v ∈ nestedCoefficientBox K
            (Dlow - wt (contactWeights w) F) w
            (T - wt residualTotalWeights F)
            (YS - wt residualYSWeights F)
            (S - wt residualSWeights F) := by
          simpa only [qF] using hdataF.2.2
        have hwidthRest : Dlow - wt (contactWeights w) F ≤
            (Dlow - delta - wt (contactWeights w) F) + delta := by
          omega
        obtain ⟨j, v, J, hv, hJ, heq, hbox, hterminal⟩ :=
          exists_power_stage_of_bandBudget_succ steps
            (Dlow - wt (contactWeights w) F)
            (Dlow - delta - wt (contactWeights w) F)
            w delta
            (T - wt residualTotalWeights F)
            (YS - wt residualYSWeights F)
            (S - wt residualSWeights F)
            hwidthRest qF hqF hqFBox F hF hsourceF
        have hwts := nested_mem_weights hbox hJ
        let jUp : Fin (Nat.succ steps + 1) := ⟨j.val + 1, by omega⟩
        have hv' : v.1 ≠ 0 := by
          intro hz
          apply hv
          exact Subtype.ext hz
        have stageF :
            HasFactorStage (Nat.succ steps + 1) Dlow w delta T YS S q F := by
          refine ⟨jUp, v.1, J, hv', hJ, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · change F ^ (j.val + 1) * J = q v.1
            calc
              F ^ (j.val + 1) * J = F * (F ^ j.val * J) := by
                rw [pow_succ']
                ring
              _ = F * qF v := by rw [heq]
              _ = qOne v := (hprodF v).symm
              _ = q v.1 := rfl
          · simpa only [jUp, sub_one_then_mul] using hwts.1
          · simpa only [jUp, sub_one_then_mul] using hwts.2.1
          · simpa only [jUp, sub_one_then_mul] using hwts.2.2.1
          · simpa only [jUp, sub_pair_then_mul] using hwts.2.2.2
          · intro hlt
            apply hterminal
            change j.val + 1 < steps + 1
            change j.val + 1 + 1 < Nat.succ steps + 1 at hlt
            omega
        exact ⟨stageF, immediate G vG hvG⟩
      · rcases honeG with ⟨⟨vF, hvF⟩, hdivG⟩
        let qG := quotientLinear qOne G hG hdivG
        have hdataG := quotientLinear_nested_data Dlow w T YS S qOne hqOne
          hqOneBox G hG hdivG
        have hqG : Function.Injective qG := by
          simpa only [qG] using hdataG.1
        have hprodG : ∀ v, qOne v = G * qG v := by
          simpa only [qG] using hdataG.2.1
        have hqGBox : ∀ v, qG v ∈ nestedCoefficientBox K
            (Dlow - wt (contactWeights w) G) w
            (T - wt residualTotalWeights G)
            (YS - wt residualYSWeights G)
            (S - wt residualSWeights G) := by
          simpa only [qG] using hdataG.2.2
        have hwidthRest : Dlow - wt (contactWeights w) G ≤
            (Dlow - delta - wt (contactWeights w) G) + delta := by
          omega
        obtain ⟨j, v, J, hv, hJ, heq, hbox, hterminal⟩ :=
          exists_power_stage_of_bandBudget_succ steps
            (Dlow - wt (contactWeights w) G)
            (Dlow - delta - wt (contactWeights w) G)
            w delta
            (T - wt residualTotalWeights G)
            (YS - wt residualYSWeights G)
            (S - wt residualSWeights G)
            hwidthRest qG hqG hqGBox G hG hsourceG
        have hwts := nested_mem_weights hbox hJ
        let jUp : Fin (Nat.succ steps + 1) := ⟨j.val + 1, by omega⟩
        have hv' : v.1 ≠ 0 := by
          intro hz
          apply hv
          exact Subtype.ext hz
        have stageG :
            HasFactorStage (Nat.succ steps + 1) Dlow w delta T YS S q G := by
          refine ⟨jUp, v.1, J, hv', hJ, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · change G ^ (j.val + 1) * J = q v.1
            calc
              G ^ (j.val + 1) * J = G * (G ^ j.val * J) := by
                rw [pow_succ']
                ring
              _ = G * qG v := by rw [heq]
              _ = qOne v := (hprodG v).symm
              _ = q v.1 := rfl
          · simpa only [jUp, sub_one_then_mul] using hwts.1
          · simpa only [jUp, sub_one_then_mul] using hwts.2.1
          · simpa only [jUp, sub_one_then_mul] using hwts.2.2.1
          · simpa only [jUp, sub_pair_then_mul] using hwts.2.2.2
          · intro hlt
            apply hterminal
            change j.val + 1 < steps + 1
            change j.val + 1 + 1 < Nat.succ steps + 1 at hlt
            omega
        exact ⟨immediate F vF hvF, stageG⟩
      · obtain ⟨v, hvF, hvG⟩ := hneither
        exact ⟨immediate F v hvF, immediate G v hvG⟩
end
end ProximityPrize.SubmissionLower.LocatorTwoFactorAvoidance
end PackedLocator_LocatorTwoFactorAvoidance
end Compact_PackedLocatorTail
