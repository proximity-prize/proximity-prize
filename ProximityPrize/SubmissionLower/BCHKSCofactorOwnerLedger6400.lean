import ProximityPrize.SubmissionLower.BCHKSWeightedSecantAudit6400
namespace ProximityPrize.SubmissionLower
namespace BCHKSCofactorOwnerLedger6400
theorem clipped_cofactor_order_le
    (m e nu r : Nat) (hproduct : m <= r + e * nu) :
    m - min m (e * nu) <= r := by
  omega
def cubicTripleWeightedCardCap
    (b1 b2 b3 k : Nat) : Nat :=
  let slots := k - b3
  let doubles := min b2 slots
  3 * b3 + 2 * doubles + min b1 (slots - doubles)
theorem cubicTripleWeightedCardCap_upper
    (b1 b2 b3 k c1 c2 : Nat)
    (hc1 : c1 <= b1) (hc2 : c2 <= b2)
    (hcard : b3 + c1 + c2 <= k) :
    3 * b3 + c1 + 2 * c2 <=
      cubicTripleWeightedCardCap b1 b2 b3 k := by
  have hb3 : b3 <= k := by omega
  unfold cubicTripleWeightedCardCap
  dsimp only
  by_cases hb2 : b2 <= k - b3
  · rw [min_eq_left hb2]
    by_cases hb1 : b1 <= k - b3 - b2
    · rw [min_eq_left hb1]
      omega
    · rw [min_eq_right (by omega : k - b3 - b2 <= b1)]
      omega
  · rw [min_eq_right (by omega : k - b3 <= b2)]
    simp only [Nat.sub_self]
    omega
theorem full_cofactor_owner_ledger
    (m e w DX M a h total rootMass : Nat)
    (hDX : DX + M = m * a)
    (hlocal : m * h <= rootMass + e * total)
    (hdegree : rootMass + e * w <= DX) :
    m * h + e * w + M <= m * a + e * total := by
  omega
theorem full_clipped_cofactor_owner_ledger
    (m e w DX M a h credit rootMass : Nat)
    (hDX : DX + M = m * a)
    (hlocal : m * h <= rootMass + credit)
    (hdegree : rootMass + e * w <= DX) :
    m * h + e * w + M <= m * a + credit := by
  omega
theorem clipped_credit_ge_factor_cost
    (m e w DX M a credit rootMass : Nat)
    (hDX : DX + M = m * a)
    (hlocal : m * a <= rootMass + credit)
    (hdegree : rootMass + e * w <= DX) :
    e * w + M <= credit := by
  have h := full_clipped_cofactor_owner_ledger
    m e w DX M a a credit rootMass hDX hlocal hdegree
  omega
theorem full_cofactor_owner_excess_ledger
    (m e w DX M a h total rootMass : Nat)
    (hDX : DX + M = m * a)
    (hlocal : m * h <= rootMass + e * total)
    (hdegree : rootMass + e * w <= DX)
    (ha : a <= h) (hw : w <= total) :
    m * (h - a) + M <= e * (total - w) := by
  have hmain := full_cofactor_owner_ledger
    m e w DX M a h total rootMass hDX hlocal hdegree
  have hha : h = (h - a) + a := by omega
  have htw : total = (total - w) + w := by omega
  rw [hha, htw] at hmain
  simp only [Nat.mul_add] at hmain
  omega
def cubicCofactorCounterE6400 : Nat := 17
def cubicCofactorCounterWeight6400 : Nat := 393213
def cubicCofactorCounterCard6400 : Nat := 189838
def cubicCofactorCounterMass6400 : Nat := 444313
lemma recorded_cubic_profile_violates_full_ledger6400 :
    ¬ (bchksSixteenthDerivativeMultiplicity6400 *
          cubicCofactorCounterCard6400 +
          cubicCofactorCounterE6400 * cubicCofactorCounterWeight6400 +
          868689 <=
        bchksSixteenthDerivativeMultiplicity6400 * 185364 +
          cubicCofactorCounterE6400 * cubicCofactorCounterMass6400) := by
  norm_num [bchksSixteenthDerivativeMultiplicity6400,
    cubicCofactorCounterCard6400, cubicCofactorCounterE6400,
    cubicCofactorCounterWeight6400, cubicCofactorCounterMass6400]
lemma recorded_cubic_profile_full_ledger_gap6400 :
    bchksSixteenthDerivativeMultiplicity6400 * (189838 - 185364) +
        868689 - 17 * (444313 - 393213) = 6630825909 := by
  norm_num [bchksSixteenthDerivativeMultiplicity6400]
def cubicClippedTransitionExponent6400 : Nat := 494026
def cubicClippedWorstCore6400 : Nat := 22487
def cubicClippedWorstDouble6400 : Nat := 162877
lemma cubic_clipped_transition_profile6400 :
    cubicClippedWorstCore6400 + cubicClippedWorstDouble6400 = 185364 ∧
      3 * cubicClippedWorstCore6400 +
          2 * cubicClippedWorstDouble6400 = 393215 ∧
      2 * cubicClippedWorstCore6400 +
          cubicClippedWorstDouble6400 <= 393213 - 131071 ∧
      cubicClippedTransitionExponent6400 * 393213 + 868689 <=
        cubicClippedWorstCore6400 *
            min bchksSixteenthDerivativeMultiplicity6400
              (3 * cubicClippedTransitionExponent6400) +
          cubicClippedWorstDouble6400 *
            min bchksSixteenthDerivativeMultiplicity6400
              (2 * cubicClippedTransitionExponent6400) := by
  norm_num [cubicClippedWorstCore6400, cubicClippedWorstDouble6400,
    cubicClippedTransitionExponent6400,
    bchksSixteenthDerivativeMultiplicity6400]
lemma cubic_clipped_last_exponent_fits6400 :
    646385 * 393213 + 868689 <=
      76778 * min bchksSixteenthDerivativeMultiplicity6400 (3 * 646385) +
        (185364 - 76778) *
          min bchksSixteenthDerivativeMultiplicity6400 (2 * 646385) := by
  norm_num [bchksSixteenthDerivativeMultiplicity6400]
lemma cubic_clipped_next_exponent_misses6400 :
    76778 * min bchksSixteenthDerivativeMultiplicity6400 (3 * 646386) +
        (185364 - 76778) *
          min bchksSixteenthDerivativeMultiplicity6400 (2 * 646386) <
      646386 * 393213 + 868689 := by
  norm_num [bchksSixteenthDerivativeMultiplicity6400]
def cubicPostCofactorE6400 : Nat := 494026
def cubicPostCofactorB16400 : Nat := 0
def cubicPostCofactorB26400 : Nat := 239657
def cubicPostCofactorB36400 : Nat := 22487
def cubicPostCofactorT6400 : Nat := 284631
def cubicPostCofactorOwnerDouble6400 : Nat := 162877
def cubicPostCofactorOutsidePivot6400 : Nat := 76780
def cubicPostCofactorPivotBlock6400 : Nat := 86097
lemma cubic_postCofactor_profile_constraints6400 :
    cubicPostCofactorB16400 + cubicPostCofactorB26400 +
        cubicPostCofactorB36400 = 262144 ∧
      cubicPostCofactorB26400 + 2 * cubicPostCofactorB36400 =
        cubicPostCofactorT6400 ∧
      207720 < 262144 ∧
      17 <= cubicPostCofactorE6400 ∧
      cubicPostCofactorE6400 * 87382 > 868689 ∧
      (cubicPostCofactorE6400 - 1) * 393213 + 868689 <
        87382 + (cubicPostCofactorE6400 - 1) *
          (131071 + 87382 + cubicPostCofactorT6400) ∧
      cubicPostCofactorB36400 + cubicPostCofactorOwnerDouble6400 =
        185364 ∧
      3 * cubicPostCofactorB36400 +
          2 * cubicPostCofactorOwnerDouble6400 = 393215 ∧
      2 * cubicPostCofactorB36400 +
          cubicPostCofactorOwnerDouble6400 <= 393213 - 131071 := by
  norm_num [cubicPostCofactorB16400, cubicPostCofactorB26400,
    cubicPostCofactorB36400, cubicPostCofactorT6400,
    cubicPostCofactorE6400, cubicPostCofactorOwnerDouble6400]
lemma cubic_postCofactor_weightedCauchy_fails6400 :
    325754 ^ 2 < 479314 * 325752 ∧
      479314 * 325752 - 325754 ^ 2 = 50021825612 := by
  norm_num
lemma cubic_postCofactor_pivotCauchy_fails6400 :
    172194 ^ 2 < 325754 * 217168 ∧
      325754 * 217168 - 172194 ^ 2 = 41092571036 := by
  norm_num
lemma cubic_postCofactor_explicit_setSystem_arithmetic6400 :
    cubicPostCofactorOutsidePivot6400 +
        cubicPostCofactorPivotBlock6400 =
      cubicPostCofactorOwnerDouble6400 ∧
      3 * cubicPostCofactorB36400 +
          2 * (cubicPostCofactorOutsidePivot6400 +
            (cubicPostCofactorPivotBlock6400 - 1)) = 393213 ∧
      cubicPostCofactorB36400 +
          (cubicPostCofactorPivotBlock6400 - 1) < 131071 ∧
      85969 + 128 = cubicPostCofactorPivotBlock6400 ∧
      85969 + 2 * 128 <= cubicPostCofactorOwnerDouble6400 ∧
      274979000000000001 < 2 ^ (128 : Nat) := by
  norm_num [cubicPostCofactorOutsidePivot6400,
    cubicPostCofactorPivotBlock6400, cubicPostCofactorOwnerDouble6400,
    cubicPostCofactorB36400]
end BCHKSCofactorOwnerLedger6400
end ProximityPrize.SubmissionLower
