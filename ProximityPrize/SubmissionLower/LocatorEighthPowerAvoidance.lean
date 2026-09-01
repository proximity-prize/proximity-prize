import ProximityPrize.SubmissionLower.LocatorSeventhPowerAvoidance

namespace ProximityPrize.SubmissionLower.LocatorEighthPowerAvoidance

open scoped BigOperators
open RCN081 RCN100 RCN119 RCN130 RCN156 RCN180 RCN234 RCN260
open LocatorLowQuotient LocatorCoprimeQuotient
open LocatorDoubleSquareAvoidance LocatorTripleCubeAvoidance
open LocatorFourthPowerAvoidance LocatorFifthPowerAvoidance
open LocatorSixthPowerAvoidance LocatorSeventhPowerAvoidance

noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000

variable {K V I : Type*} [Field K]
local instance : DecidableEq K := Classical.decEq K

section LinearDichotomy

variable [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- Compact adapter for the public seven-way extractor. -/
private theorem exists_low_not_dvd_before_seventh_or_seventh_low
    (Dhigh Dlow w delta T YS S : ℕ)
    (hwidth : Dhigh ≤ Dlow + delta)
    (q : V →ₗ[K] MvPolynomial (Fin 4) K) (hq : Function.Injective q)
    (hmem : ∀ v, q v ∈ nestedCoefficientBox K Dhigh w T YS S)
    (F : MvPolynomial (Fin 4) K) (hF : F ≠ 0)
    (hsource :
      delta * channelCount T YS S +
          delta * channelCount
            (T - wt residualTotalWeights F) (YS - wt residualYSWeights F)
              (S - wt residualSWeights F) +
          delta * channelCount
            (T - 2 * wt residualTotalWeights F)
              (YS - 2 * wt residualYSWeights F)
              (S - 2 * wt residualSWeights F) +
          delta * channelCount
            (T - 3 * wt residualTotalWeights F)
              (YS - 3 * wt residualYSWeights F)
              (S - 3 * wt residualSWeights F) +
          delta * channelCount
            (T - 4 * wt residualTotalWeights F)
              (YS - 4 * wt residualYSWeights F)
              (S - 4 * wt residualSWeights F) +
          delta * channelCount
            (T - 5 * wt residualTotalWeights F)
              (YS - 5 * wt residualYSWeights F)
              (S - 5 * wt residualSWeights F) +
          delta * channelCount
            (T - 6 * wt residualTotalWeights F)
              (YS - 6 * wt residualYSWeights F)
              (S - 6 * wt residualSWeights F) <
        Module.finrank K V) :
    ∃ (j : Fin 7) (v : V) (Q : MvPolynomial (Fin 4) K),
      v ≠ 0 ∧ Q ≠ 0 ∧ F ^ j.val * Q = q v ∧
      (j.val < 6 → ¬ F ∣ Q) ∧
      Q ∈ nestedCoefficientBox K
        (Dlow - j.val * delta - j.val * wt (contactWeights w) F) w
        (T - j.val * wt residualTotalWeights F)
        (YS - j.val * wt residualYSWeights F)
        (S - j.val * wt residualSWeights F) := by
  rcases
      LocatorSeventhPowerAvoidance.exists_first_low_not_dvd_or_second_low_not_dvd_or_third_low_not_dvd_or_fourth_low_not_dvd_or_fifth_low_not_dvd_or_sixth_low_not_dvd_or_seventh_low
        Dhigh Dlow w delta T YS S hwidth q hq hmem F hF hsource with
    h0 | h1 | h2 | h3 | h4 | h5 | h6
  · obtain ⟨v, hv, hQ, hbox, hndiv⟩ := h0
    refine ⟨⟨0, by decide⟩, v, q v, hv, hQ, by simp, ?_, ?_⟩
    · intro _
      exact hndiv
    · simpa using hbox
  · obtain ⟨v, Q, hv, hQ, heq, hndiv, hbox⟩ := h1
    refine ⟨⟨1, by decide⟩, v, Q, hv, hQ, ?_, ?_, ?_⟩
    · simpa using heq
    · intro _
      exact hndiv
    · simpa using hbox
  · obtain ⟨v, Q, hv, hQ, heq, hndiv, hbox⟩ := h2
    refine ⟨⟨2, by decide⟩, v, Q, hv, hQ, ?_, ?_, ?_⟩
    · calc
        F ^ 2 * Q = F * (F * Q) := by ring
        _ = q v := heq
    · intro _
      exact hndiv
    · simpa using hbox
  · obtain ⟨v, Q, hv, hQ, heq, hndiv, hbox⟩ := h3
    refine ⟨⟨3, by decide⟩, v, Q, hv, hQ, ?_, ?_, ?_⟩
    · calc
        F ^ 3 * Q = F * (F * (F * Q)) := by ring
        _ = q v := heq
    · intro _
      exact hndiv
    · simpa using hbox
  · obtain ⟨v, Q, hv, hQ, heq, hndiv, hbox⟩ := h4
    refine ⟨⟨4, by decide⟩, v, Q, hv, hQ, ?_, ?_, ?_⟩
    · calc
        F ^ 4 * Q = F * (F * (F * (F * Q))) := by ring
        _ = q v := heq
    · intro _
      exact hndiv
    · simpa using hbox
  · obtain ⟨v, Q, hv, hQ, heq, hndiv, hbox⟩ := h5
    refine ⟨⟨5, by decide⟩, v, Q, hv, hQ, ?_, ?_, ?_⟩
    · calc
        F ^ 5 * Q = F * (F * (F * (F * (F * Q)))) := by ring
        _ = q v := heq
    · intro _
      exact hndiv
    · simpa using hbox
  · obtain ⟨v, Q, hv, hQ, heq, hbox⟩ := h6
    refine ⟨⟨6, by decide⟩, v, Q, hv, hQ, ?_, ?_, ?_⟩
    · calc
        F ^ 6 * Q = F * (F * (F * (F * (F * (F * Q))))) := by ring
        _ = q v := heq
    · intro hj
      change 6 < 6 at hj
      omega
    · simpa using hbox

/-- Eight-stage repeated projection, packaged by the exact power at which the
first low quotient escapes divisibility.  The final `j = 7` arm carries no
nondivisibility claim. -/
theorem exists_low_not_dvd_before_eighth_or_eighth_low
    (Dhigh Dlow w delta T YS S : ℕ)
    (hwidth : Dhigh ≤ Dlow + delta)
    (q : V →ₗ[K] MvPolynomial (Fin 4) K) (hq : Function.Injective q)
    (hmem : ∀ v, q v ∈ nestedCoefficientBox K Dhigh w T YS S)
    (F : MvPolynomial (Fin 4) K) (hF : F ≠ 0)
    (hsource :
      delta * channelCount T YS S +
          delta * channelCount (T - wt residualTotalWeights F)
            (YS - wt residualYSWeights F) (S - wt residualSWeights F) +
          delta * channelCount (T - 2 * wt residualTotalWeights F)
            (YS - 2 * wt residualYSWeights F) (S - 2 * wt residualSWeights F) +
          delta * channelCount (T - 3 * wt residualTotalWeights F)
            (YS - 3 * wt residualYSWeights F) (S - 3 * wt residualSWeights F) +
          delta * channelCount (T - 4 * wt residualTotalWeights F)
            (YS - 4 * wt residualYSWeights F) (S - 4 * wt residualSWeights F) +
          delta * channelCount (T - 5 * wt residualTotalWeights F)
            (YS - 5 * wt residualYSWeights F) (S - 5 * wt residualSWeights F) +
          delta * channelCount (T - 6 * wt residualTotalWeights F)
            (YS - 6 * wt residualYSWeights F) (S - 6 * wt residualSWeights F) +
          delta * channelCount (T - 7 * wt residualTotalWeights F)
            (YS - 7 * wt residualYSWeights F) (S - 7 * wt residualSWeights F) <
        Module.finrank K V) :
    ∃ (j : Fin 8) (v : V) (Q : MvPolynomial (Fin 4) K),
      v ≠ 0 ∧ Q ≠ 0 ∧ F ^ j.val * Q = q v ∧
      (j.val < 7 → ¬ F ∣ Q) ∧
      Q ∈ nestedCoefficientBox K
        (Dlow - j.val * delta - j.val * wt (contactWeights w) F) w
        (T - j.val * wt residualTotalWeights F)
        (YS - j.val * wt residualYSWeights F)
        (S - j.val * wt residualSWeights F) := by
  classical
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
      delta * channelCount (T - wt residualTotalWeights F)
          (YS - wt residualYSWeights F) (S - wt residualSWeights F) +
        delta * channelCount (T - 2 * wt residualTotalWeights F)
          (YS - 2 * wt residualYSWeights F) (S - 2 * wt residualSWeights F) +
        delta * channelCount (T - 3 * wt residualTotalWeights F)
          (YS - 3 * wt residualYSWeights F) (S - 3 * wt residualSWeights F) +
        delta * channelCount (T - 4 * wt residualTotalWeights F)
          (YS - 4 * wt residualYSWeights F) (S - 4 * wt residualSWeights F) +
        delta * channelCount (T - 5 * wt residualTotalWeights F)
          (YS - 5 * wt residualYSWeights F) (S - 5 * wt residualSWeights F) +
        delta * channelCount (T - 6 * wt residualTotalWeights F)
          (YS - 6 * wt residualYSWeights F) (S - 6 * wt residualSWeights F) +
        delta * channelCount (T - 7 * wt residualTotalWeights F)
          (YS - 7 * wt residualYSWeights F) (S - 7 * wt residualSWeights F) <
      Module.finrank K lowOne := by
    have hsum := bandOne.finrank_range_add_finrank_ker
    change Module.finrank K bandOne.range + Module.finrank K lowOne =
      Module.finrank K V at hsum
    omega
  let qOne : lowOne →ₗ[K] MvPolynomial (Fin 4) K := q.comp lowOne.subtype
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
      simpa only [bandOne, qOne, LinearMap.comp_apply, Submodule.coe_subtype]
        using hv
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
          (T - wt residualTotalWeights F) (YS - wt residualYSWeights F)
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
          (hqOneBox v) (recon_eq_mul_quotientPolynomial qOne F hdivOne v)
    let TOne := T - wt residualTotalWeights F
    let YOne := YS - wt residualYSWeights F
    let SOne := S - wt residualSWeights F
    let DOneHigh := Dlow - wt (contactWeights w) F
    let DOneLow := Dlow - delta - wt (contactWeights w) F
    have hwidthRest : DOneHigh ≤ DOneLow + delta := by
      simp only [DOneHigh, DOneLow]
      omega
    have hsourceRest :
        delta * channelCount TOne YOne SOne +
          delta * channelCount (TOne - wt residualTotalWeights F)
            (YOne - wt residualYSWeights F) (SOne - wt residualSWeights F) +
          delta * channelCount (TOne - 2 * wt residualTotalWeights F)
            (YOne - 2 * wt residualYSWeights F) (SOne - 2 * wt residualSWeights F) +
          delta * channelCount (TOne - 3 * wt residualTotalWeights F)
            (YOne - 3 * wt residualYSWeights F) (SOne - 3 * wt residualSWeights F) +
          delta * channelCount (TOne - 4 * wt residualTotalWeights F)
            (YOne - 4 * wt residualYSWeights F) (SOne - 4 * wt residualSWeights F) +
          delta * channelCount (TOne - 5 * wt residualTotalWeights F)
            (YOne - 5 * wt residualYSWeights F) (SOne - 5 * wt residualSWeights F) +
          delta * channelCount (TOne - 6 * wt residualTotalWeights F)
            (YOne - 6 * wt residualYSWeights F) (SOne - 6 * wt residualSWeights F) <
        Module.finrank K lowOne := by
      simp only [TOne, YOne, SOne]
      have hT2 : T - wt residualTotalWeights F - wt residualTotalWeights F =
          T - 2 * wt residualTotalWeights F := by omega
      have hY2 : YS - wt residualYSWeights F - wt residualYSWeights F =
          YS - 2 * wt residualYSWeights F := by omega
      have hS2 : S - wt residualSWeights F - wt residualSWeights F =
          S - 2 * wt residualSWeights F := by omega
      have hT3 : T - wt residualTotalWeights F - 2 * wt residualTotalWeights F =
          T - 3 * wt residualTotalWeights F := by omega
      have hY3 : YS - wt residualYSWeights F - 2 * wt residualYSWeights F =
          YS - 3 * wt residualYSWeights F := by omega
      have hS3 : S - wt residualSWeights F - 2 * wt residualSWeights F =
          S - 3 * wt residualSWeights F := by omega
      have hT4 : T - wt residualTotalWeights F - 3 * wt residualTotalWeights F =
          T - 4 * wt residualTotalWeights F := by omega
      have hY4 : YS - wt residualYSWeights F - 3 * wt residualYSWeights F =
          YS - 4 * wt residualYSWeights F := by omega
      have hS4 : S - wt residualSWeights F - 3 * wt residualSWeights F =
          S - 4 * wt residualSWeights F := by omega
      have hT5 : T - wt residualTotalWeights F - 4 * wt residualTotalWeights F =
          T - 5 * wt residualTotalWeights F := by omega
      have hY5 : YS - wt residualYSWeights F - 4 * wt residualYSWeights F =
          YS - 5 * wt residualYSWeights F := by omega
      have hS5 : S - wt residualSWeights F - 4 * wt residualSWeights F =
          S - 5 * wt residualSWeights F := by omega
      have hT6 : T - wt residualTotalWeights F - 5 * wt residualTotalWeights F =
          T - 6 * wt residualTotalWeights F := by omega
      have hY6 : YS - wt residualYSWeights F - 5 * wt residualYSWeights F =
          YS - 6 * wt residualYSWeights F := by omega
      have hS6 : S - wt residualSWeights F - 5 * wt residualSWeights F =
          S - 6 * wt residualSWeights F := by omega
      have hT7 : T - wt residualTotalWeights F - 6 * wt residualTotalWeights F =
          T - 7 * wt residualTotalWeights F := by omega
      have hY7 : YS - wt residualYSWeights F - 6 * wt residualYSWeights F =
          YS - 7 * wt residualYSWeights F := by omega
      have hS7 : S - wt residualSWeights F - 6 * wt residualSWeights F =
          S - 7 * wt residualSWeights F := by omega
      simpa only [hT2, hY2, hS2, hT3, hY3, hS3, hT4, hY4, hS4,
        hT5, hY5, hS5, hT6, hY6, hS6, hT7, hY7, hS7]
        using hlowOneRank
    obtain ⟨j, v, Q, hv, hQ, heq, hndvd, hbox⟩ :=
      exists_low_not_dvd_before_seventh_or_seventh_low
        DOneHigh DOneLow w delta TOne YOne SOne hwidthRest qTwo hqTwo
          hqTwoBox F hF hsourceRest
    let j8 : Fin 8 := ⟨j.val + 1, by omega⟩
    refine ⟨j8, v.1, Q, ?_, hQ, ?_, ?_, ?_⟩
    · intro hz
      exact hv (Subtype.ext hz)
    · calc
        F ^ j8.val * Q = F * (F ^ j.val * Q) := by
          simp only [j8]
          rw [pow_succ']
          ring
        _ = F * qTwo v := by rw [heq]
        _ = qOne v :=
          (recon_eq_mul_quotientPolynomial qOne F hdivOne v).symm
        _ = q v.1 := rfl
    · intro hj
      exact hndvd (by simp only [j8] at hj ⊢; omega)
    · have hD : DOneLow - j.val * delta -
            j.val * wt (contactWeights w) F =
          Dlow - j8.val * delta - j8.val * wt (contactWeights w) F := by
          simp only [DOneLow, j8, Nat.sub_sub]
          congr 1
          ring
      have hT : TOne - j.val * wt residualTotalWeights F =
          T - j8.val * wt residualTotalWeights F := by
        change T - wt residualTotalWeights F -
            j.val * wt residualTotalWeights F =
          T - (j.val + 1) * wt residualTotalWeights F
        rw [Nat.add_mul, Nat.one_mul]
        omega
      have hY : YOne - j.val * wt residualYSWeights F =
          YS - j8.val * wt residualYSWeights F := by
        change YS - wt residualYSWeights F -
            j.val * wt residualYSWeights F =
          YS - (j.val + 1) * wt residualYSWeights F
        rw [Nat.add_mul, Nat.one_mul]
        omega
      have hS : SOne - j.val * wt residualSWeights F =
          S - j8.val * wt residualSWeights F := by
        change S - wt residualSWeights F -
            j.val * wt residualSWeights F =
          S - (j.val + 1) * wt residualSWeights F
        rw [Nat.add_mul, Nat.one_mul]
        omega
      simpa only [hD, hT, hY, hS] using hbox
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
    let j0 : Fin 8 := ⟨0, by decide⟩
    refine ⟨j0, v.1, q v.1, hv, hqv, ?_, ?_, ?_⟩
    · simp [j0]
    · intro _
      simpa only [qOne, LinearMap.comp_apply, Submodule.coe_subtype] using hvdiv
    · simpa only [j0, Nat.zero_mul, Nat.sub_zero, qOne,
        LinearMap.comp_apply, Submodule.coe_subtype] using hqOneBox v

end LinearDichotomy

/-- Iterated derivative in the residual `R` coordinate. -/
def pderivRIter : ℕ → MvPolynomial (Fin 4) K → MvPolynomial (Fin 4) K
  | 0, H => H
  | n + 1, H => MvPolynomial.pderiv (2 : Fin 4) (pderivRIter n H)

theorem pderivRIter_ne_zero_of_le {a b : ℕ}
    (hab : a ≤ b) (H : MvPolynomial (Fin 4) K)
    (h : pderivRIter b H ≠ 0) : pderivRIter a H ≠ 0 := by
  induction b with
  | zero =>
      have ha : a = 0 := by omega
      subst a
      exact h
  | succ b ih =>
      by_cases hab' : a ≤ b
      · apply ih hab'
        intro hz
        apply h
        simp [pderivRIter, hz]
      · have : a = b + 1 := by omega
        subst a
        exact h

theorem pderivRIter_weight_add_le {w : ℕ} (n : ℕ)
    (H : MvPolynomial (Fin 4) K) (h : pderivRIter n H ≠ 0) :
    wt (contactWeights w) (pderivRIter n H) + n * (w - 1) ≤
      wt (contactWeights w) H := by
  induction n with
  | zero => simp [pderivRIter]
  | succ n ih =>
      have hn : pderivRIter n H ≠ 0 :=
        pderivRIter_ne_zero_of_le (Nat.le_succ n) H h
      have hwgt := LocatorContact.pderiv_R_weight_add_le
        (contactWeights w) (pderivRIter n H) h
      have hi := ih hn
      change wt (contactWeights w)
          (MvPolynomial.pderiv (2 : Fin 4) (pderivRIter n H)) + (w - 1) ≤
        wt (contactWeights w) (pderivRIter n H) at hwgt
      simp only [pderivRIter]
      rw [Nat.add_mul, Nat.one_mul]
      omega

section EighthDerivative

variable [Fintype I]
local instance : DecidableEq I := Classical.decEq I

theorem specialization_pderiv_R8_eq_zero_of_kernel_low_box
    (D Dlow w L s m : ℕ) (nodes : I ↪ K) (u0 u1 : I → K)
    (v : ConstraintKernel (K := K) D w L s m nodes u0 u1)
    (hlow : reconstruct K D w L s v.1 ∈ globalCoefficientBox K Dlow w L s)
    (P : Polynomial K) (gamma : K) (support : Finset I)
    (hw : 1 ≤ w) (hP : P.natDegree ≤ w)
    (hcapacity : Dlow ≤ (m - 8) * support.card + 8 * (w - 1))
    (hvalues : ∀ i ∈ support, P.eval (nodes i) = u0 i + gamma * u1 i) :
    RCN319.specialization K P gamma
      (pderivRIter 8 (reconstruct K D w L s v.1)) = 0 := by
  classical
  let H := reconstruct K D w L s v.1
  by_contra hne
  have hder8 : pderivRIter 8 H ≠ 0 := by
    intro hz
    apply hne
    rw [hz, map_zero]
  have hH : H ≠ 0 := by
    have h := pderivRIter_ne_zero_of_le (a := 0) (b := 8)
      (by decide) H hder8
    simpa only [pderivRIter] using h
  have hder7 : pderivRIter 7 H ≠ 0 :=
    pderivRIter_ne_zero_of_le (a := 7) (b := 8) (by decide) H hder8
  have hDlow : 0 < Dlow := by
    obtain ⟨d, hd⟩ := MvPolynomial.support_nonempty.mpr hH
    have h := (hlow hd).2.2
    omega
  have hHweight : wt (contactWeights w) H ≤ Dlow - 1 :=
    ((mem_flagGlobalCoefficientBox_iff H Dlow w L s hDlow).mp hlow).2.2
  have hiterWeight := pderivRIter_weight_add_le (w := w) 7 H hder7
  have hder7weight : wt (contactWeights w) (pderivRIter 7 H) ≤
      Dlow - 1 - 7 * (w - 1) := by omega
  have hdegree := ContactOrderBridge.specialized_R_derivative_degree K
    (pderivRIter 7 H) P gamma w (Dlow - 1 - 7 * (w - 1))
    hP hder7weight hne
  have hdegreeStrict :
      (RCN122.specialization K P gamma (pderivRIter 8 H)).natDegree <
        (m - 8) * support.card := by
    rw [RCN101.specialization_eq_ordinary]
    rw [RCN101.specialization_eq_ordinary] at hdegree
    simp only [pderivRIter] at hdegree ⊢
    omega
  have hcontact : ∀ i ∈ support, ∀ r : ℕ,
      slopeDifference K ^ (m - 8 - r) ∣
        (RCN122.homogenizedTranslation K (nodes i) (u0 i) (u1 i)
          (pderivRIter 8 H)).coeff r := by
    intro i _
    apply (ContactOrderBridge.contactAtLeast_iff_block_divisibility
      K (nodes i) (u0 i) (u1 i) (m - 8) _).mp
    have h0 := ContactOrderBridge.contactAtLeast_of_mem_kernel
      K D w L s m nodes u0 u1 v.1 v.2 i
    have h1 := ContactOrderBridge.contactAtLeast_pderiv_R
      K (nodes i) (u0 i) (u1 i) m H h0
    have h2 := ContactOrderBridge.contactAtLeast_pderiv_R
      K (nodes i) (u0 i) (u1 i) (m - 1) (pderivRIter 1 H) h1
    have h3 := ContactOrderBridge.contactAtLeast_pderiv_R
      K (nodes i) (u0 i) (u1 i) (m - 2) (pderivRIter 2 H) h2
    have h4 := ContactOrderBridge.contactAtLeast_pderiv_R
      K (nodes i) (u0 i) (u1 i) (m - 3) (pderivRIter 3 H) h3
    have h5 := ContactOrderBridge.contactAtLeast_pderiv_R
      K (nodes i) (u0 i) (u1 i) (m - 4) (pderivRIter 4 H) h4
    have h6 := ContactOrderBridge.contactAtLeast_pderiv_R
      K (nodes i) (u0 i) (u1 i) (m - 5) (pderivRIter 5 H) h5
    have h7 := ContactOrderBridge.contactAtLeast_pderiv_R
      K (nodes i) (u0 i) (u1 i) (m - 6) (pderivRIter 6 H) h6
    have h8 := ContactOrderBridge.contactAtLeast_pderiv_R
      K (nodes i) (u0 i) (u1 i) (m - 7) (pderivRIter 7 H) h7
    simpa only [pderivRIter, Nat.sub_sub] using h8
  have hz := RCN122.specialization_eq_zero_of_contact_and_degree K
    (pderivRIter 8 H) P gamma nodes u0 u1 support (m - 8)
    hcontact hvalues hdegreeStrict
  apply hne
  simpa only [H, RCN101.specialization_eq_ordinary] using hz

theorem specialization_eq_zero_of_pderiv_R8_eighth_product
    (P : Polynomial K) (gamma : K) (F Q : MvPolynomial (Fin 4) K)
    (hfactorial : (40320 : K) ≠ 0)
    (hFzero : RCN319.specialization K P gamma F = 0)
    (hregular : RCN319.specialization K P gamma
      (MvPolynomial.pderiv (2 : Fin 4) F) ≠ 0)
    (heighth : RCN319.specialization K P gamma
      (pderivRIter 8 (F ^ 8 * Q)) = 0) :
    RCN319.specialization K P gamma Q = 0 := by
  have hfactorialPoly : (40320 : Polynomial K) ≠ 0 := by
    intro hz
    apply hfactorial
    have heval := congrArg (Polynomial.eval 0) hz
    simpa using heval
  let dR : MvPolynomial (Fin 4) K → MvPolynomial (Fin 4) K :=
    MvPolynomial.pderiv (2 : Fin 4)
  let G : MvPolynomial (Fin 4) K := F ^ 7 * Q
  have hG0 : RCN319.specialization K P gamma (dR^[0] G) = 0 := by
    simp only [Function.iterate_zero_apply, G, map_mul, map_pow, hFzero,
      zero_pow (show (7 : Nat) ≠ 0 by decide), zero_mul]
  have hG1 : RCN319.specialization K P gamma (dR^[1] G) = 0 := by
    simp (config := { maxSteps := 300000 }) only [dR, G,
      Function.iterate_one, MvPolynomial.pderiv_mul, MvPolynomial.pderiv_pow,
      map_add, map_mul, map_pow, map_natCast, hFzero,
      zero_pow (show (7 : Nat) ≠ 0 by decide),
      zero_mul, mul_zero, zero_add, add_zero]
    norm_num
  have hG2 : RCN319.specialization K P gamma (dR^[2] G) = 0 := by
    simp (config := { maxSteps := 300000 }) only [dR, G,
      Function.iterate_succ_apply', Function.iterate_zero_apply,
      Function.iterate_one, MvPolynomial.pderiv_mul, MvPolynomial.pderiv_pow,
      map_add, map_mul, map_pow, map_natCast, hFzero,
      zero_pow (show (7 : Nat) ≠ 0 by decide),
      zero_mul, mul_zero, zero_add, add_zero]
    ring
  have hG3 : RCN319.specialization K P gamma (dR^[3] G) = 0 := by
    simp (config := { maxSteps := 300000 }) only [dR, G,
      Function.iterate_succ_apply', Function.iterate_zero_apply,
      Function.iterate_one, MvPolynomial.pderiv_mul, MvPolynomial.pderiv_pow,
      map_add, map_mul, map_pow, map_natCast, hFzero,
      zero_pow (show (7 : Nat) ≠ 0 by decide),
      zero_mul, mul_zero, zero_add, add_zero]
    ring
  have hG4 : RCN319.specialization K P gamma (dR^[4] G) = 0 := by
    simp (config := { maxSteps := 300000 }) only [dR, G,
      Function.iterate_succ_apply', Function.iterate_zero_apply,
      Function.iterate_one, MvPolynomial.pderiv_mul, MvPolynomial.pderiv_pow,
      map_add, map_mul, map_pow, map_natCast, hFzero,
      zero_pow (show (7 : Nat) ≠ 0 by decide),
      zero_mul, mul_zero, zero_add, add_zero]
    ring
  have hG5 : RCN319.specialization K P gamma (dR^[5] G) = 0 := by
    simp (config := { maxSteps := 300000 }) only [dR, G,
      Function.iterate_succ_apply', Function.iterate_zero_apply,
      Function.iterate_one, MvPolynomial.pderiv_mul, MvPolynomial.pderiv_pow,
      map_add, map_mul, map_pow, map_natCast, hFzero,
      zero_pow (show (7 : Nat) ≠ 0 by decide),
      zero_mul, mul_zero, zero_add, add_zero]
    ring
  have hG6 : RCN319.specialization K P gamma (dR^[6] G) = 0 := by
    simp (config := { maxSteps := 600000 }) only [dR, G,
      Function.iterate_succ_apply', Function.iterate_zero_apply,
      Function.iterate_one, MvPolynomial.pderiv_mul, MvPolynomial.pderiv_pow,
      map_add, map_mul, map_pow, map_natCast, hFzero,
      zero_pow (show (7 : Nat) ≠ 0 by decide),
      zero_mul, mul_zero, zero_add, add_zero]
    ring
  have hG7 : RCN319.specialization K P gamma (dR^[7] G) =
      (5040 : Polynomial K) *
        (RCN319.specialization K P gamma (dR F)) ^ 7 *
        RCN319.specialization K P gamma Q := by
    simp (config := { maxSteps := 900000 }) only [dR, G,
      Function.iterate_succ_apply', Function.iterate_zero_apply,
      Function.iterate_one, MvPolynomial.pderiv_mul, MvPolynomial.pderiv_pow,
      map_add, map_mul, map_pow, map_natCast, hFzero,
      zero_pow (show (7 : Nat) ≠ 0 by decide),
      zero_mul, mul_zero, zero_add, add_zero, mul_add]
    ring
  change RCN319.specialization K P gamma G = 0 at hG0
  change RCN319.specialization K P gamma
      (MvPolynomial.pderiv (2 : Fin 4) G) = 0 at hG1
  change RCN319.specialization K P gamma
      (MvPolynomial.pderiv (2 : Fin 4)
        (MvPolynomial.pderiv (2 : Fin 4) G)) = 0 at hG2
  change RCN319.specialization K P gamma
      (MvPolynomial.pderiv (2 : Fin 4)
        (MvPolynomial.pderiv (2 : Fin 4)
          (MvPolynomial.pderiv (2 : Fin 4) G))) = 0 at hG3
  change RCN319.specialization K P gamma
      (MvPolynomial.pderiv (2 : Fin 4)
        (MvPolynomial.pderiv (2 : Fin 4)
          (MvPolynomial.pderiv (2 : Fin 4)
            (MvPolynomial.pderiv (2 : Fin 4) G)))) = 0 at hG4
  change RCN319.specialization K P gamma
      (MvPolynomial.pderiv (2 : Fin 4)
        (MvPolynomial.pderiv (2 : Fin 4)
          (MvPolynomial.pderiv (2 : Fin 4)
            (MvPolynomial.pderiv (2 : Fin 4)
              (MvPolynomial.pderiv (2 : Fin 4) G))))) = 0 at hG5
  change RCN319.specialization K P gamma
      (MvPolynomial.pderiv (2 : Fin 4)
        (MvPolynomial.pderiv (2 : Fin 4)
          (MvPolynomial.pderiv (2 : Fin 4)
            (MvPolynomial.pderiv (2 : Fin 4)
              (MvPolynomial.pderiv (2 : Fin 4)
                (MvPolynomial.pderiv (2 : Fin 4) G)))))) = 0 at hG6
  change RCN319.specialization K P gamma
      (MvPolynomial.pderiv (2 : Fin 4)
        (MvPolynomial.pderiv (2 : Fin 4)
          (MvPolynomial.pderiv (2 : Fin 4)
            (MvPolynomial.pderiv (2 : Fin 4)
              (MvPolynomial.pderiv (2 : Fin 4)
                (MvPolynomial.pderiv (2 : Fin 4)
                  (MvPolynomial.pderiv (2 : Fin 4) G))))))) =
      (5040 : Polynomial K) *
        (RCN319.specialization K P gamma
          (MvPolynomial.pderiv (2 : Fin 4) F)) ^ 7 *
        RCN319.specialization K P gamma Q at hG7
  have hprod : F ^ 8 * Q = F * G := by
    simp only [G]
    ring
  rw [hprod] at heighth
  change RCN319.specialization K P gamma (dR^[8] (F * G)) = 0 at heighth
  have hmul : (40320 : Polynomial K) *
      (RCN319.specialization K P gamma
        (MvPolynomial.pderiv (2 : Fin 4) F)) ^ 8 *
      RCN319.specialization K P gamma Q = 0 := by
    simp (config := { maxSteps := 600000 }) only [dR,
      Function.iterate_succ_apply', Function.iterate_zero_apply,
      Function.iterate_one, MvPolynomial.pderiv_mul, map_add, map_mul,
      hFzero, hG0, hG1, hG2, hG3, hG4, hG5, hG6, hG7,
      zero_mul, mul_zero, zero_add, add_zero] at heighth
    ring_nf at heighth ⊢
    exact heighth
  have hcoef : (40320 : Polynomial K) *
      (RCN319.specialization K P gamma
        (MvPolynomial.pderiv (2 : Fin 4) F)) ^ 8 ≠ 0 :=
    mul_ne_zero hfactorialPoly (pow_ne_zero 8 hregular)
  exact (mul_eq_zero.mp hmul).resolve_left hcoef

end EighthDerivative

end

end ProximityPrize.SubmissionLower.LocatorEighthPowerAvoidance
