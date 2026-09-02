/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ProximityPrize.Benchmark.TargetUpper

/-!
# Singular-contact and ninth-multiplicity gates

The accepted lower `67.77` proof recovers a quotient from the eighth residual
derivative at every regular contact.  Its two algebraic escape hatches are a
contact at which that first residual derivative vanishes, or a factor occurring
with multiplicity at least nine.

This file records the exact upper-side local algebra.  A support locator made
from distinct evaluation points is regular at every selected point, in every
characteristic.  Conversely, ninth multiplicity really does annihilate the
eighth derivative, so it cannot be dismissed formally; the companion exact
frontier audit counts the dyadic families in which such multiplicity is
automatic.

The final section gives a generic incidence gate for a fixed carrier restricted
to an affine challenge line.  Outside nodes where both the carrier and its
residual derivative vanish identically along the line, a degree-`d` carrier has
at most `d` singular challenge values per node.
-/

namespace ProximityPrize.SubmissionUpper.SingularMultiplicityGate

open Polynomial

section Locator

variable {F : Type*} [Field F]

noncomputable def supportLocator (S : Finset F) : Polynomial F :=
  ∏ a ∈ S, (Polynomial.X - Polynomial.C a)

/-- A square-free support locator is regular at each selected point. -/
theorem supportLocator_derivative_eval_ne_zero
    [DecidableEq F] (S : Finset F) {x : F} (hx : x ∈ S) :
    (supportLocator S).derivative.eval x ≠ 0 := by
  classical
  rw [supportLocator]
  change Polynomial.eval x
    (Polynomial.derivative
      (Multiset.map (fun a ↦ Polynomial.X - Polynomial.C a) S.1).prod) ≠ 0
  rw [Polynomial.eval_multiset_prod_X_sub_C_derivative
    (S := S.1) (r := x) hx]
  apply Multiset.prod_ne_zero
  intro hzero
  rw [Multiset.mem_map] at hzero
  obtain ⟨a, ha, hxa⟩ := hzero
  have : x = a := sub_eq_zero.mp hxa
  subst a
  exact S.2.notMem_erase ha

/-- Nine copies of a linear factor survive eight ordinary derivatives, so the
eighth derivative still vanishes at the factor root. -/
theorem eighth_derivative_eval_eq_zero_of_ninth_factor
    {P : Polynomial F} {x : F}
    (hfactor : (Polynomial.X - Polynomial.C x) ^ 9 ∣ P) :
    (Polynomial.derivative^[8] P).eval x = 0 := by
  have hdvd : Polynomial.X - Polynomial.C x ∣
      Polynomial.derivative^[8] P := by
    simpa using
      (Polynomial.pow_sub_dvd_iterate_derivative_of_pow_dvd (p := P)
        (q := Polynomial.X - Polynomial.C x) 8 hfactor)
  exact Polynomial.dvd_iff_isRoot.mp hdvd

/-- The benchmark characteristic does not annihilate the first ninth-stage
coefficient. -/
theorem koalaBear_ninth_factorial_nonzero_receipt :
    362880 % 2130706433 ≠ 0 := by
  norm_num

end Locator

section Incidence

variable {K I : Type*} [Field K] [Fintype K] [DecidableEq K]

/-- Challenges at which both a carrier and its residual derivative vanish. -/
noncomputable def singularChallenges
    (value residualDerivative : I → Polynomial K) (i : I) : Finset K :=
  (Finset.univ.filter fun gamma ↦
    (value i).eval gamma = 0 ∧ (residualDerivative i).eval gamma = 0)

/-- At a noncommon node, simultaneous carrier/derivative vanishing is bounded
by either nonzero polynomial's degree. -/
theorem singularChallenges_card_le
    (value residualDerivative : I → Polynomial K) (degreeCap : ℕ)
    (hdegree : ∀ i,
      (value i).natDegree ≤ degreeCap ∧
        (residualDerivative i).natDegree ≤ degreeCap)
    (i : I) (hnoncommon : value i ≠ 0 ∨ residualDerivative i ≠ 0) :
    (singularChallenges value residualDerivative i).card ≤ degreeCap := by
  classical
  rcases hnoncommon with hvalue | hderivative
  · calc
      (singularChallenges value residualDerivative i).card ≤
          (value i).roots.toFinset.card := by
        apply Finset.card_le_card
        intro gamma hgamma
        rw [Multiset.mem_toFinset, Polynomial.mem_roots hvalue]
        exact (Finset.mem_filter.mp (show gamma ∈
          Finset.univ.filter (fun eta ↦
            (value i).eval eta = 0 ∧
              (residualDerivative i).eval eta = 0) by
                simpa only [singularChallenges] using hgamma)).2.1
      _ ≤ (value i).natDegree := by
        exact (Multiset.toFinset_card_le _).trans (Polynomial.card_roots' _)
      _ ≤ degreeCap := (hdegree i).1
  · calc
      (singularChallenges value residualDerivative i).card ≤
          (residualDerivative i).roots.toFinset.card := by
        apply Finset.card_le_card
        intro gamma hgamma
        rw [Multiset.mem_toFinset, Polynomial.mem_roots hderivative]
        exact (Finset.mem_filter.mp (show gamma ∈
          Finset.univ.filter (fun eta ↦
            (value i).eval eta = 0 ∧
              (residualDerivative i).eval eta = 0) by
                simpa only [singularChallenges] using hgamma)).2.2
      _ ≤ (residualDerivative i).natDegree := by
        exact (Multiset.toFinset_card_le _).trans (Polynomial.card_roots' _)
      _ ≤ degreeCap := (hdegree i).2

/-- If every challenge chooses a noncommon singular node, the challenge set
has size at most `|I| * degreeCap`.  This packages the root bound independently
of how the node is selected. -/
theorem challenge_card_le_of_noncommon_singular_choice
    [Fintype I]
    (value residualDerivative : I → Polynomial K) (degreeCap : ℕ)
    (hdegree : ∀ i,
      (value i).natDegree ≤ degreeCap ∧
        (residualDerivative i).natDegree ≤ degreeCap)
    (Gamma : Finset K) (chosenNode : K → I)
    (hsingular : ∀ gamma ∈ Gamma,
      gamma ∈ singularChallenges value residualDerivative (chosenNode gamma))
    (hnoncommon : ∀ gamma ∈ Gamma,
      value (chosenNode gamma) ≠ 0 ∨
        residualDerivative (chosenNode gamma) ≠ 0) :
    Gamma.card ≤ Fintype.card I * degreeCap := by
  classical
  calc
    Gamma.card = ∑ i : I, (Gamma.filter fun gamma ↦ chosenNode gamma = i).card := by
      have hsum := Finset.sum_card_fiberwise_eq_card_filter Gamma
        (Finset.univ : Finset I) chosenNode
      simpa using hsum.symm
    _ ≤ ∑ _i : I, degreeCap := by
      apply Finset.sum_le_sum
      intro i _
      by_cases hi : (Gamma.filter fun gamma ↦ chosenNode gamma = i).Nonempty
      · obtain ⟨gamma, hgamma⟩ := hi
        have hgammaGamma := (Finset.mem_filter.mp hgamma).1
        have hnode := (Finset.mem_filter.mp hgamma).2
        apply (Finset.card_le_card ?_).trans
          (singularChallenges_card_le value residualDerivative degreeCap hdegree i ?_)
        · intro eta heta
          have hetaGamma := (Finset.mem_filter.mp heta).1
          have hetanode := (Finset.mem_filter.mp heta).2
          simpa only [hetanode] using hsingular eta hetaGamma
        · simpa only [hnode] using hnoncommon gamma hgammaGamma
      · rw [Finset.not_nonempty_iff_eq_empty.mp hi]
        simp
    _ = Fintype.card I * degreeCap := by simp

def domainSize : ℕ := 262144
def legalCarrierDegree : ℕ := 262144
def challengeThreshold : ℕ := 274980728111395088
def baseFieldCardinality : ℕ := 2130706433

def exactProductFibreMaximum : ℕ :=
  6417043898306465355817890560136032291335107637534903232761973368781765385

/-- Even granting the full domain degree at every node, noncommon singular
contacts are many orders of magnitude below the winning threshold. -/
theorem benchmark_noncommon_singular_capacity_lt_threshold :
    domainSize * legalCarrierDegree < challengeThreshold := by
  norm_num [domainSize, legalCarrierDegree, challengeThreshold]

/-- Exact degree/agreement ledger of the best automatic high-multiplicity
dyadic cell.  It can be realized with `T = Y^16`, so the origin multiplicity
is already sixteen; its obstruction is selector entropy, not degree. -/
theorem best_dyadic_multiplicity_cell_receipt :
    8 < 16 ∧
      (136 - 6 - 3) * 1024 = 130048 ∧
      130048 + 1023 = 131071 ∧
      136 * 1024 + 1023 = 140287 ∧
      139782 ≤ 140287 := by
  norm_num

/-- The exact largest product residue in the 256-label cell is short by a
factor strictly between four and five after the six top pins. -/
theorem exact_product_fibre_deficit_receipt :
    4 * exactProductFibreMaximum <
        baseFieldCardinality ^ 6 * challengeThreshold ∧
      baseFieldCardinality ^ 6 * challengeThreshold <
        5 * exactProductFibreMaximum := by
  norm_num [exactProductFibreMaximum, baseFieldCardinality, challengeThreshold]

/-- A base-field Frobenius chart is too small, while the quadratic subfield is
the first subfield large enough to hold a winning challenge set. -/
theorem subfield_challenge_window_receipt :
    baseFieldCardinality < challengeThreshold ∧
      challengeThreshold < baseFieldCardinality ^ 2 := by
  norm_num [baseFieldCardinality, challengeThreshold]

/-- In a degree-six extension, Frobenius conjugate roots trade at exactly `d`
base-field pins per extra root for each proper subfield degree `d`. -/
theorem frobenius_pin_trade_receipt :
    6 - 1 = 1 * (6 / 1 - 1) ∧
      6 - 2 = 2 * (6 / 2 - 1) ∧
      6 - 3 = 3 * (6 / 3 - 1) := by
  norm_num

end Incidence

#print axioms supportLocator_derivative_eval_ne_zero
#print axioms eighth_derivative_eval_eq_zero_of_ninth_factor
#print axioms challenge_card_le_of_noncommon_singular_choice
#print axioms benchmark_noncommon_singular_capacity_lt_threshold
#print axioms best_dyadic_multiplicity_cell_receipt
#print axioms exact_product_fibre_deficit_receipt
#print axioms frobenius_pin_trade_receipt

end ProximityPrize.SubmissionUpper.SingularMultiplicityGate
