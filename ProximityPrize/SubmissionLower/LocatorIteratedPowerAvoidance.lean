/-
Level-generic power avoidance.

Provenance.  This file is adapted from the public submission of `BitWonka`
(PR #465 in `proximity-prize/proximity-prize`), which builds on an earlier
revision of this tree, so the `RCN*` and `Locator*` names it refers to are
unchanged here.


`LocatorSecondPowerAvoidance` … `LocatorEighthPowerAvoidance` each unroll one
extra stage of the same three ingredients.  This file proves all three at an
arbitrary level `n`, by induction, so that no further hand-unrolled level files
are needed.

* `contactAtLeast_pderivRIter` — contact order drops by at most one per
  `R`-derivative.
* `specialization_pderivRIter_eq_zero_of_kernel_low_box` — the `n`-th iterated
  `R`-derivative of a low-box kernel reconstruction specializes to zero.
* `pderivRIter_power_split` — the Leibniz identity `d^[n] (F^(n+m) * Q) =
  (n+m).descFactorial n * (F^m * (dF)^n * Q) + F^(m+1) * S`.
* `specialization_eq_zero_of_pderivRIter_power_product` — the level-`n`
  cancellation, replacing the per-level `…_product` theorems.
* `exists_low_not_dvd_iter` — the level-`n` repeated-projection dichotomy,
  replacing `exists_low_not_dvd_before_*_or_*_low`.
-/

import ProximityPrize.SubmissionLower.LocatorEighthPowerAvoidance

namespace ProximityPrize.SubmissionLower.LocatorIteratedPowerAvoidance

open scoped BigOperators
open RCN081 RCN100 RCN119 RCN130 RCN156 RCN180 RCN234 RCN260
open LocatorLowQuotient LocatorCoprimeQuotient
open LocatorDoubleSquareAvoidance LocatorTripleCubeAvoidance
open LocatorFourthPowerAvoidance LocatorFifthPowerAvoidance
open LocatorSixthPowerAvoidance LocatorSeventhPowerAvoidance
open LocatorEighthPowerAvoidance

noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

variable {K V I : Type*} [Field K]
local instance : DecidableEq K := Classical.decEq K

/-! ### Contact order under iterated `R`-differentiation -/

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

theorem contactAtLeast_pderivRIter (x u0 u1 : K) (m : ℕ)
    (H : MvPolynomial (Fin 4) K)
    (h : ContactOrderBridge.ContactAtLeast K x u0 u1 m H) (n : ℕ) :
    ContactOrderBridge.ContactAtLeast K x u0 u1 (m - n) (pderivRIter n H) := by
  induction n with
  | zero => simpa [pderivRIter] using h
  | succ n ih =>
      have hstep := ContactOrderBridge.contactAtLeast_pderiv_R
        (K := K) x u0 u1 (m - n) (pderivRIter n H) ih
      simpa only [pderivRIter, Nat.sub_sub] using hstep

/-! ### The Leibniz split -/

theorem pderivRIter_succ_inner (n : ℕ) (H : MvPolynomial (Fin 4) K) :
    pderivRIter (n + 1) H = pderivRIter n (MvPolynomial.pderiv (2 : Fin 4) H) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      show MvPolynomial.pderiv (2 : Fin 4) (pderivRIter (n + 1) H) =
        pderivRIter (n + 1) (MvPolynomial.pderiv (2 : Fin 4) H)
      rw [ih]
      rfl

section Leibniz

variable (F : MvPolynomial (Fin 4) K)

theorem pderiv_pow_succ_mul (j : ℕ) (Q : MvPolynomial (Fin 4) K) :
    MvPolynomial.pderiv (2 : Fin 4) (F ^ (j + 1) * Q) =
      F ^ j * (((j + 1 : ℕ) : MvPolynomial (Fin 4) K) *
          (MvPolynomial.pderiv (2 : Fin 4) F * Q) +
        F * MvPolynomial.pderiv (2 : Fin 4) Q) := by
  rw [MvPolynomial.pderiv_mul, MvPolynomial.pderiv_pow]
  simp only [Nat.add_sub_cancel]
  push_cast
  ring

/-- `d^[n] (F^(n+m) * Q)`, expanded around its leading term.  The leading
coefficient is the descending factorial `(n+m)(n+m-1)…(m+1)`, and every other
term still carries a factor of `F`. -/
theorem pderivRIter_power_split (n : ℕ) :
    ∀ (m : ℕ) (Q : MvPolynomial (Fin 4) K),
      ∃ S : MvPolynomial (Fin 4) K,
        pderivRIter n (F ^ (n + m) * Q) =
          ((n + m).descFactorial n : MvPolynomial (Fin 4) K) *
              (F ^ m * (MvPolynomial.pderiv (2 : Fin 4) F) ^ n * Q) +
            F ^ (m + 1) * S := by
  induction n with
  | zero =>
      intro m Q
      refine ⟨0, ?_⟩
      simp [pderivRIter]
  | succ n ih =>
      intro m Q
      set dF := MvPolynomial.pderiv (2 : Fin 4) F with hdF
      set Q' : MvPolynomial (Fin 4) K :=
        ((n + m + 1 : ℕ) : MvPolynomial (Fin 4) K) * (dF * Q) +
          F * MvPolynomial.pderiv (2 : Fin 4) Q with hQ'
      have hshape : n + 1 + m = (n + m) + 1 := by omega
      have hpeel :
          pderivRIter (n + 1) (F ^ (n + 1 + m) * Q) =
            pderivRIter n (F ^ (n + m) * Q') := by
        rw [pderivRIter_succ_inner, hshape, hQ', hdF,
          pderiv_pow_succ_mul F (n + m) Q]
      rw [hpeel]
      obtain ⟨S, hS⟩ := ih m Q'
      refine ⟨((n + m).descFactorial n : MvPolynomial (Fin 4) K) *
          (dF ^ n * MvPolynomial.pderiv (2 : Fin 4) Q) + S, ?_⟩
      rw [hS, hQ']
      have hfac : ((n + 1 + m).descFactorial (n + 1) : ℕ) =
          (n + m + 1) * (n + m).descFactorial n := by
        rw [hshape, Nat.succ_descFactorial_succ]
      rw [hfac]
      push_cast
      ring

end Leibniz

/-! ### Level-`n` cancellation -/

theorem specialization_eq_zero_of_pderivRIter_power_product
    (n : ℕ) (P : Polynomial K) (gamma : K) (F Q : MvPolynomial (Fin 4) K)
    (hfactorial : ((Nat.factorial n : ℕ) : K) ≠ 0)
    (hFzero : RCN319.specialization K P gamma F = 0)
    (hregular : RCN319.specialization K P gamma
      (MvPolynomial.pderiv (2 : Fin 4) F) ≠ 0)
    (hiter : RCN319.specialization K P gamma
      (pderivRIter n (F ^ n * Q)) = 0) :
    RCN319.specialization K P gamma Q = 0 := by
  obtain ⟨S, hS⟩ := pderivRIter_power_split (K := K) F n 0 Q
  rw [show n + 0 = n from rfl] at hS
  rw [hS] at hiter
  simp only [pow_zero, one_mul, map_add, map_mul, map_pow,
    map_natCast, hFzero, zero_pow (show (0 + 1 : ℕ) ≠ 0 by decide),
    zero_mul, add_zero] at hiter
  have hfacPoly : ((Nat.factorial n : ℕ) : Polynomial K) ≠ 0 := by
    intro hz
    apply hfactorial
    have heval := congrArg (Polynomial.eval 0) hz
    simpa using heval
  have hdesc : (n.descFactorial n : ℕ) = Nat.factorial n :=
    Nat.descFactorial_self n
  rw [hdesc] at hiter
  have hcoef : ((Nat.factorial n : ℕ) : Polynomial K) *
      (RCN319.specialization K P gamma
        (MvPolynomial.pderiv (2 : Fin 4) F)) ^ n ≠ 0 :=
    mul_ne_zero hfacPoly (pow_ne_zero n hregular)
  have hmul : ((Nat.factorial n : ℕ) : Polynomial K) *
      (RCN319.specialization K P gamma
        (MvPolynomial.pderiv (2 : Fin 4) F)) ^ n *
      RCN319.specialization K P gamma Q = 0 := by
    rw [mul_assoc]
    exact hiter
  exact (mul_eq_zero.mp hmul).resolve_left hcoef


/-! ### Level-`n` repeated projection -/

section LinearDichotomy

variable [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- The `n`-fold repeated projection, packaged by the exact power at which the
first low quotient escapes divisibility.  The `j = n` arm carries no
nondivisibility claim.  This is the level-generic form of the
`exists_low_not_dvd_before_*_or_*_low` family. -/
theorem exists_low_not_dvd_iter (n : ℕ)
    (Dhigh Dlow w delta T YS S : ℕ)
    (hwidth : Dhigh ≤ Dlow + delta)
    (q : V →ₗ[K] MvPolynomial (Fin 4) K) (hq : Function.Injective q)
    (hmem : ∀ v, q v ∈ nestedCoefficientBox K Dhigh w T YS S)
    (F : MvPolynomial (Fin 4) K) (hF : F ≠ 0)
    (hsource : ∑ i ∈ Finset.range (n + 1),
        delta * channelCount (T - i * wt residualTotalWeights F)
          (YS - i * wt residualYSWeights F)
          (S - i * wt residualSWeights F) < Module.finrank K V) :
    ∃ (j : ℕ) (v : V) (Q : MvPolynomial (Fin 4) K),
      j ≤ n ∧ v ≠ 0 ∧ Q ≠ 0 ∧ F ^ j * Q = q v ∧
      (j < n → ¬ F ∣ Q) ∧
      Q ∈ nestedCoefficientBox K
        (Dlow - j * delta - j * wt (contactWeights w) F) w
        (T - j * wt residualTotalWeights F)
        (YS - j * wt residualYSWeights F)
        (S - j * wt residualSWeights F) := by
  classical
  induction n generalizing V Dhigh Dlow T YS S with
  | zero =>
      have hrank : delta * channelCount T YS S < Module.finrank K V := by
        simpa using hsource
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
      have hsum := bandOne.finrank_range_add_finrank_ker
      change Module.finrank K bandOne.range + Module.finrank K lowOne =
        Module.finrank K V at hsum
      have hpos : 0 < Module.finrank K lowOne := by omega
      have hnt : Nontrivial lowOne := Module.finrank_pos_iff.mp hpos
      obtain ⟨v, hv⟩ := exists_ne (0 : lowOne)
      have hv1 : v.1 ≠ 0 := fun hz => hv (Subtype.ext hz)
      have hqv : q v.1 ≠ 0 := by
        intro hz
        exact hv1 (hq (by simpa only [map_zero] using hz))
      have hbox : q v.1 ∈ nestedCoefficientBox K Dlow w T YS S := by
        have hzero : highBandMap w Dlow delta T YS S (q v.1) = 0 := by
          have hvk := v.2
          change bandOne v.1 = 0 at hvk
          simpa only [bandOne, LinearMap.comp_apply] using hvk
        exact mem_low_of_highBandMap_eq_zero Dhigh Dlow w delta T YS S hwidth
          (q v.1) (hmem v.1) hzero
      refine ⟨0, v.1, q v.1, le_rfl, hv1, hqv, by simp, ?_, ?_⟩
      · intro hj; exact absurd hj (by omega)
      · simpa only [Nat.zero_mul, Nat.sub_zero] using hbox
  | succ n ih =>
      have hshiftT : ∀ i : ℕ, T - wt residualTotalWeights F - i * wt residualTotalWeights F = T - (i + 1) * wt residualTotalWeights F := by
        intro i; rw [Nat.succ_mul, ← Nat.sub_sub]; omega
      have hshiftY : ∀ i : ℕ, YS - wt residualYSWeights F - i * wt residualYSWeights F = YS - (i + 1) * wt residualYSWeights F := by
        intro i; rw [Nat.succ_mul, ← Nat.sub_sub]; omega
      have hshiftS : ∀ i : ℕ, S - wt residualSWeights F - i * wt residualSWeights F = S - (i + 1) * wt residualSWeights F := by
        intro i; rw [Nat.succ_mul, ← Nat.sub_sub]; omega
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
      have hsum := bandOne.finrank_range_add_finrank_ker
      change Module.finrank K bandOne.range + Module.finrank K lowOne =
        Module.finrank K V at hsum
      have hsplit : ∑ i ∈ Finset.range (n + 1 + 1),
            delta * channelCount (T - i * wt residualTotalWeights F) (YS - i * wt residualYSWeights F) (S - i * wt residualSWeights F) =
          (∑ i ∈ Finset.range (n + 1),
            delta * channelCount (T - (i + 1) * wt residualTotalWeights F) (YS - (i + 1) * wt residualYSWeights F)
              (S - (i + 1) * wt residualSWeights F)) + delta * channelCount T YS S := by
        rw [Finset.sum_range_succ']
        simp
      have hlowOneRank : (∑ i ∈ Finset.range (n + 1),
          delta * channelCount (T - (i + 1) * wt residualTotalWeights F) (YS - (i + 1) * wt residualYSWeights F)
            (S - (i + 1) * wt residualSWeights F)) < Module.finrank K lowOne := by
        rw [hsplit] at hsource
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
          have hvk := v.2
          change bandOne v.1 = 0 at hvk
          simpa only [bandOne, LinearMap.comp_apply] using hvk
        simpa only [qOne, LinearMap.comp_apply, Submodule.coe_subtype] using
          mem_low_of_highBandMap_eq_zero Dhigh Dlow w delta T YS S hwidth
            (q v.1) (hmem v.1) hzero
      by_cases hdivOne : ∀ v : lowOne, F ∣ qOne v
      · let qTwo := quotientLinear qOne F hF hdivOne
        have hqTwo : Function.Injective qTwo :=
          quotientLinear_injective qOne hqOne F hF hdivOne
        have hqTwoBox : ∀ v : lowOne,
            qTwo v ∈ nestedCoefficientBox K
              (Dlow - wt (contactWeights w) F) w (T - wt residualTotalWeights F) (YS - wt residualYSWeights F) (S - wt residualSWeights F) := by
          intro v
          by_cases hv : v = 0
          · subst v
            rw [map_zero]
            exact (nestedCoefficientBox K _ _ _ _ _).zero_mem
          · have hqOneV : qOne v ≠ 0 := by
              intro hz
              exact hv (hqOne (by simpa only [map_zero] using hz))
            have hqTwoV : qTwo v ≠ 0 := by
              intro hz
              apply hqOneV
              rw [recon_eq_mul_quotientPolynomial qOne F hdivOne v]
              change F * qTwo v = 0
              rw [hz, mul_zero]
            exact quotient_mem_nestedCoefficientBox_of_mul_eq
              (qOne v) F (qTwo v) Dlow w T YS S hqOneV hF hqTwoV
              (hqOneBox v) (recon_eq_mul_quotientPolynomial qOne F hdivOne v)
        have hwidthRest : Dlow - wt (contactWeights w) F ≤
            (Dlow - delta - wt (contactWeights w) F) + delta := by omega
        have hsourceRest : ∑ i ∈ Finset.range (n + 1),
            delta * channelCount (T - wt residualTotalWeights F - i * wt residualTotalWeights F) (YS - wt residualYSWeights F - i * wt residualYSWeights F)
              (S - wt residualSWeights F - i * wt residualSWeights F) < Module.finrank K lowOne := by
          have hcongr : ∀ i ∈ Finset.range (n + 1),
              delta * channelCount (T - wt residualTotalWeights F - i * wt residualTotalWeights F) (YS - wt residualYSWeights F - i * wt residualYSWeights F)
                  (S - wt residualSWeights F - i * wt residualSWeights F) =
                delta * channelCount (T - (i + 1) * wt residualTotalWeights F) (YS - (i + 1) * wt residualYSWeights F)
                  (S - (i + 1) * wt residualSWeights F) := by
            intro i _
            rw [hshiftT i, hshiftY i, hshiftS i]
          rw [Finset.sum_congr rfl hcongr]
          exact hlowOneRank
        obtain ⟨j, v, Q, hjle, hv, hQ, heq, hndvd, hbox⟩ :=
          ih (Dlow - wt (contactWeights w) F)
            (Dlow - delta - wt (contactWeights w) F) (T - wt residualTotalWeights F) (YS - wt residualYSWeights F) (S - wt residualSWeights F)
            hwidthRest qTwo hqTwo hqTwoBox hsourceRest
        refine ⟨j + 1, v.1, Q, by omega, ?_, hQ, ?_, ?_, ?_⟩
        · intro hz
          exact hv (Subtype.ext hz)
        · calc
            F ^ (j + 1) * Q = F * (F ^ j * Q) := by rw [pow_succ']; ring
            _ = F * qTwo v := by rw [heq]
            _ = qOne v :=
              (recon_eq_mul_quotientPolynomial qOne F hdivOne v).symm
            _ = q v.1 := rfl
        · intro hj
          exact hndvd (by omega)
        · have hD : Dlow - delta - wt (contactWeights w) F - j * delta -
                j * wt (contactWeights w) F =
              Dlow - (j + 1) * delta - (j + 1) * wt (contactWeights w) F := by
            rw [Nat.succ_mul, Nat.succ_mul]
            omega
          have hT : T - wt residualTotalWeights F - j * wt residualTotalWeights F = T - (j + 1) * wt residualTotalWeights F := hshiftT j
          have hY : YS - wt residualYSWeights F - j * wt residualYSWeights F = YS - (j + 1) * wt residualYSWeights F := hshiftY j
          have hS : S - wt residualSWeights F - j * wt residualSWeights F = S - (j + 1) * wt residualSWeights F := hshiftS j
          simpa only [hD, hT, hY, hS] using hbox
      · push Not at hdivOne
        obtain ⟨v, hvdiv⟩ := hdivOne
        have hv : v.1 ≠ 0 := by
          intro hz
          apply hvdiv
          have hvzero : v = 0 := Subtype.ext hz
          rw [hvzero, map_zero]
          exact dvd_zero F
        have hqv : q v.1 ≠ 0 := by
          intro hz
          exact hv (hq (by simpa only [map_zero] using hz))
        refine ⟨0, v.1, q v.1, by omega, hv, hqv, by simp, ?_, ?_⟩
        · intro _
          simpa only [qOne, LinearMap.comp_apply, Submodule.coe_subtype]
            using hvdiv
        · simpa only [Nat.zero_mul, Nat.sub_zero, qOne,
            LinearMap.comp_apply, Submodule.coe_subtype] using hqOneBox v

end LinearDichotomy


/-! ### Level-`n` kernel-box vanishing -/

section IteratedDerivative

variable [Fintype I]
local instance : DecidableEq I := Classical.decEq I

/-- Level-generic form of `specialization_pderiv_R8_eq_zero_of_kernel_low_box`:
the `(nn+1)`-st iterated `R`-derivative of a low-box kernel reconstruction
specializes to zero, provided the contact budget covers `nn + 1` stages. -/
theorem specialization_pderivRIter_eq_zero_of_kernel_low_box
    (nn D Dlow w L s m : ℕ) (nodes : I ↪ K) (u0 u1 : I → K)
    (v : ConstraintKernel (K := K) D w L s m nodes u0 u1)
    (hlow : reconstruct K D w L s v.1 ∈ globalCoefficientBox K Dlow w L s)
    (P : Polynomial K) (gamma : K) (support : Finset I)
    (hw : 1 ≤ w) (hP : P.natDegree ≤ w)
    (hcapacity : Dlow ≤ (m - (nn + 1)) * support.card + (nn + 1) * (w - 1))
    (hvalues : ∀ i ∈ support, P.eval (nodes i) = u0 i + gamma * u1 i) :
    RCN319.specialization K P gamma
      (pderivRIter (nn + 1) (reconstruct K D w L s v.1)) = 0 := by
  classical
  let H := reconstruct K D w L s v.1
  by_contra hne
  have hderS : pderivRIter (nn + 1) H ≠ 0 := by
    intro hz
    apply hne
    rw [hz, map_zero]
  have hH : H ≠ 0 := by
    have h := pderivRIter_ne_zero_of_le (a := 0) (b := nn + 1)
      (by omega) H hderS
    simpa only [pderivRIter] using h
  have hder : pderivRIter nn H ≠ 0 :=
    pderivRIter_ne_zero_of_le (a := nn) (b := nn + 1) (by omega) H hderS
  have hDlow : 0 < Dlow := by
    obtain ⟨d, hd⟩ := MvPolynomial.support_nonempty.mpr hH
    have h := (hlow hd).2.2
    omega
  have hHweight : wt (contactWeights w) H ≤ Dlow - 1 :=
    ((mem_flagGlobalCoefficientBox_iff H Dlow w L s hDlow).mp hlow).2.2
  have hiterWeight := pderivRIter_weight_add_le (w := w) nn H hder
  have hderweight : wt (contactWeights w) (pderivRIter nn H) ≤
      Dlow - 1 - nn * (w - 1) := by omega
  have hne' : RCN319.specialization K P gamma
      (MvPolynomial.pderiv (2 : Fin 4) (pderivRIter nn H)) ≠ 0 := by
    simpa only [pderivRIter] using hne
  have hdegree := ContactOrderBridge.specialized_R_derivative_degree K
    (pderivRIter nn H) P gamma w (Dlow - 1 - nn * (w - 1)) hP hderweight hne'
  have hsplit : (nn + 1) * (w - 1) = nn * (w - 1) + (w - 1) := by ring
  have hdegreeStrict :
      (RCN122.specialization K P gamma (pderivRIter (nn + 1) H)).natDegree <
        (m - (nn + 1)) * support.card := by
    rw [RCN101.specialization_eq_ordinary]
    rw [RCN101.specialization_eq_ordinary] at hdegree
    simp only [pderivRIter] at hdegree ⊢
    omega
  have hcontact : ∀ i ∈ support, ∀ r : ℕ,
      slopeDifference K ^ (m - (nn + 1) - r) ∣
        (RCN122.homogenizedTranslation K (nodes i) (u0 i) (u1 i)
          (pderivRIter (nn + 1) H)).coeff r := by
    intro i _
    apply (ContactOrderBridge.contactAtLeast_iff_block_divisibility
      K (nodes i) (u0 i) (u1 i) (m - (nn + 1)) _).mp
    have h0 := ContactOrderBridge.contactAtLeast_of_mem_kernel
      K D w L s m nodes u0 u1 v.1 v.2 i
    exact contactAtLeast_pderivRIter (nodes i) (u0 i) (u1 i) m H h0 (nn + 1)
  have hz := RCN122.specialization_eq_zero_of_contact_and_degree K
    (pderivRIter (nn + 1) H) P gamma nodes u0 u1 support (m - (nn + 1))
    hcontact hvalues hdegreeStrict
  apply hne
  simpa only [H, RCN101.specialization_eq_ordinary] using hz

end IteratedDerivative

end

end ProximityPrize.SubmissionLower.LocatorIteratedPowerAvoidance
