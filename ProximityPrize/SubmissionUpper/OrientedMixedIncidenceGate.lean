/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ProximityPrize.Benchmark.TargetUpper

/-!
# Oriented mixed-incidence gate at the worst Source-C profile

The accepted unequal-degree incidence ledger uses the coordinatewise maximum
of a left agreement-degree vector and a right agreement-degree vector.  In
the actual proper-cut proof, however, the agreement polynomial is constructed
from the left carrier factor.  The accepted `surface_agreement_caps` lemma
first bounds it by the left vector and only then widens that bound with three
applications of `le_max_left`.

This upper-only file records the arithmetic consequence of retaining that
orientation.  At the exhaustive audit's worst Source-C depth-three,
stage-one profile, the symmetric cap is just above the regular-layer gate,
whereas the left-oriented cap is far below it.  The semantic premise still
needed by an upper attack is an oriented proper-cut incidence theorem for its
own fixed carrier family; this file neither imports nor asserts the lower
theorem.

For comparison, it also records two fallback facts.  Removing the complete
large-pencil/error term cannot close the symmetric gap.  In contrast, the
accepted flag-trapezoid correlation in the `Y,R` support would reduce the
mixed `Z`-projection degree by `19 * 44 = 836`; only `574` units are needed.
-/

namespace ProximityPrize.SubmissionUpper.OrientedMixedIncidenceGate

open scoped BigOperators

def domainSize : ℕ := 262144
def rowDegree : ℕ := 131071
def targetAgreement : ℕ := 139782
def errors : ℕ := domainSize - targetAgreement
def gap : ℕ := targetAgreement - rowDegree
def movingNodes : ℕ := domainSize - rowDegree

/-- Factor degrees at the exhaustive symmetric maximum. -/
def leftY : ℕ := 85
def leftR : ℕ := 19
def leftZ : ℕ := 2916

/-- Source-C residual degrees after the first quotient stage. -/
def rightY : ℕ := 297 - leftY
def rightR : ℕ := 63 - leftR
def rightZ : ℕ := 169536 - leftZ

def leftAgreementY : ℕ := 1 + 2 * rowDegree * leftY
def leftAgreementR : ℕ := rowDegree * (2 * leftR - 1)
def leftAgreementZ : ℕ := 2 * rowDegree * leftZ + 1

def rightAgreementY : ℕ := 1 + 2 * rowDegree * rightY
def rightAgreementR : ℕ := rowDegree * (2 * rightR - 1)
def rightAgreementZ : ℕ := 2 * rowDegree * rightZ + 1

def symmetricAgreementY : ℕ := max leftAgreementY rightAgreementY
def symmetricAgreementR : ℕ := max leftAgreementR rightAgreementR
def symmetricAgreementZ : ℕ := max leftAgreementZ rightAgreementZ

def mixedY : ℕ := leftR * rightZ + leftZ * rightR
def mixedR : ℕ := leftY * rightZ + leftZ * rightY
def mixedZ : ℕ := leftY * rightR + leftR * rightY

def symmetricDot : ℕ :=
  symmetricAgreementY * mixedY + symmetricAgreementR * mixedR +
    symmetricAgreementZ * mixedZ

def orientedDot : ℕ :=
  leftAgreementY * mixedY + leftAgreementR * mixedR +
    leftAgreementZ * mixedZ

def pencilTerm : ℕ := (errors + 1) * gap * mixedZ
def symmetricNumerator : ℕ := movingNodes * symmetricDot + pencilTerm
def orientedNumerator : ℕ := movingNodes * orientedDot + pencilTerm
def symmetricCap : ℕ := symmetricNumerator / gap
def orientedCap : ℕ := orientedNumerator / gap

def strictRegularLayerGate : ℕ := 10019053654770474

/-- Cardinality target for the agreement-`139782` upper attack. -/
def challengeThreshold : ℕ := 274980728111395088

/-- Terminal contribution already available from the upper jet-layer route. -/
def terminalCap : ℕ := 4466279432592298

/-- Number of regular layers in the existing upper jet-layer cover. -/
def regularLayerCount : ℕ := 27

/-- Exact transcription of the worst profile's degree arithmetic. -/
theorem profile_receipt :
    (rightY, rightR, rightZ) = (212, 44, 166620) ∧
      (leftAgreementY, leftAgreementR, leftAgreementZ) =
        (22282071, 4849627, 764406073) ∧
      (rightAgreementY, rightAgreementR, rightAgreementZ) =
        (55574105, 11403177, 43678100041) ∧
      (mixedY, mixedR, mixedZ) = (3294084, 14780892, 7768) := by
  norm_num [rightY, rightR, rightZ, leftY, leftR, leftZ,
    leftAgreementY, leftAgreementR, leftAgreementZ,
    rightAgreementY, rightAgreementR, rightAgreementZ, rowDegree,
    mixedY, mixedR, mixedZ]

/-- Every symmetric maximum chooses the right degree, even though the
agreement polynomial in the oriented proper-cut call comes from the left. -/
theorem right_agreement_strictly_dominates :
    leftAgreementY < rightAgreementY ∧
      leftAgreementR < rightAgreementR ∧
      leftAgreementZ < rightAgreementZ := by
  norm_num [leftAgreementY, leftAgreementR, leftAgreementZ,
    rightAgreementY, rightAgreementR, rightAgreementZ, rightY, rightR,
    rightZ, leftY, leftR, leftZ, rowDegree]

theorem numerator_receipt :
    symmetricDot = 690906378907192 ∧
      orientedDot = 151018732870312 ∧
      pencilTerm = 8279942994424 ∧
      symmetricNumerator = 90559180082445371440 ∧
      orientedNumerator = 19794486653453399200 := by
  norm_num [symmetricDot, orientedDot, pencilTerm, symmetricNumerator,
    orientedNumerator, symmetricAgreementY, symmetricAgreementR,
    symmetricAgreementZ, leftAgreementY, leftAgreementR, leftAgreementZ,
    rightAgreementY, rightAgreementR, rightAgreementZ, mixedY, mixedR,
    mixedZ, errors, gap, movingNodes, domainSize, targetAgreement, rowDegree,
    rightY, rightR, rightZ, leftY, leftR, leftZ]

theorem cap_receipt :
    symmetricCap = 10395956845648647 ∧
      orientedCap = 2272355258116565 := by
  norm_num [symmetricCap, orientedCap, symmetricNumerator,
    orientedNumerator, symmetricDot, orientedDot, pencilTerm,
    symmetricAgreementY, symmetricAgreementR, symmetricAgreementZ,
    leftAgreementY, leftAgreementR, leftAgreementZ, rightAgreementY,
    rightAgreementR, rightAgreementZ, mixedY, mixedR, mixedZ, errors, gap,
    movingNodes, domainSize, targetAgreement, rowDegree, rightY, rightR,
    rightZ, leftY, leftR, leftZ]

/-- The left-oriented cap closes the regular layer by a wide margin. -/
theorem oriented_cap_lt_layer_gate : orientedCap < strictRegularLayerGate := by
  norm_num [cap_receipt, strictRegularLayerGate]

/-- Semantic handoff: any upper incidence theorem with the oriented numerator
immediately puts the layer below the required gate. -/
theorem card_lt_layer_gate_of_oriented_incidence (card : ℕ)
    (hcard : card * gap ≤ orientedNumerator) :
    card < strictRegularLayerGate := by
  norm_num [gap, orientedNumerator, orientedDot, pencilTerm,
    leftAgreementY, leftAgreementR, leftAgreementZ, mixedY, mixedR, mixedZ,
    errors, movingNodes, domainSize, targetAgreement, rowDegree, rightY,
    rightR, rightZ, leftY, leftR, leftZ] at hcard
  norm_num [strictRegularLayerGate]
  omega

/-- Exact numerator saving required to turn the symmetric floor quotient into
a strict layer bound. -/
def requiredNumeratorSaving : ℕ :=
  symmetricNumerator - (strictRegularLayerGate * gap - 1)

theorem required_saving_receipt :
    requiredNumeratorSaving = 3283203695739772427 := by
  norm_num [requiredNumeratorSaving, symmetricNumerator, symmetricDot,
    pencilTerm, symmetricAgreementY, symmetricAgreementR,
    symmetricAgreementZ, leftAgreementY, leftAgreementR, leftAgreementZ,
    rightAgreementY, rightAgreementR, rightAgreementZ, mixedY, mixedR,
    mixedZ, strictRegularLayerGate, gap, errors, movingNodes, domainSize,
    targetAgreement, rowDegree, rightY, rightR, rightZ, leftY, leftR, leftZ]

/-- Even deleting the complete error/large-pencil charge is insufficient by
more than five orders of magnitude. -/
theorem deleting_pencil_term_is_insufficient :
    pencilTerm < requiredNumeratorSaving := by
  norm_num [pencilTerm, required_saving_receipt, errors, gap, mixedZ,
    domainSize, targetAgreement, rowDegree, rightY, rightR, leftY, leftR]

def oneMixedZUnitSaving : ℕ :=
  movingNodes * symmetricAgreementZ + (errors + 1) * gap

/-- `574` is the smallest pure mixed-`Z` degree saving that closes the
symmetric gap. -/
theorem minimal_mixedZ_saving_receipt :
    573 * oneMixedZUnitSaving < requiredNumeratorSaving ∧
      requiredNumeratorSaving ≤ 574 * oneMixedZUnitSaving := by
  norm_num [oneMixedZUnitSaving, required_saving_receipt, movingNodes,
    symmetricAgreementZ, leftAgreementZ, rightAgreementZ, errors, gap,
    domainSize, targetAgreement, rowDegree, rightZ, leftZ]

/-- The nested `Y+R` trapezoids replace the rectangular mixed degree `7768`
by `7768 - 19*44 = 6932`, a saving of `836`. -/
def flagMixedZ : ℕ := mixedZ - leftR * rightR
def flagMixedZSaving : ℕ := mixedZ - flagMixedZ

theorem flag_mixedZ_receipt :
    flagMixedZ = 6932 ∧ flagMixedZSaving = 836 := by
  norm_num [flagMixedZ, flagMixedZSaving, mixedZ, leftY, leftR, rightY,
    rightR]

def flagRefinedNumerator : ℕ :=
  symmetricNumerator - flagMixedZSaving * oneMixedZUnitSaving
def flagRefinedCap : ℕ := flagRefinedNumerator / gap

/-- The flag-trapezoid `Z` saving alone would also close the layer, without
using the stronger left-oriented agreement vector. -/
theorem flag_refined_cap_receipt :
    flagRefinedCap = 9846523108732647 ∧
      flagRefinedCap < strictRegularLayerGate := by
  norm_num [flagRefinedCap, flagRefinedNumerator, symmetricNumerator,
    symmetricDot, pencilTerm, flagMixedZSaving, flagMixedZ,
    oneMixedZUnitSaving, symmetricAgreementY, symmetricAgreementR,
    symmetricAgreementZ, leftAgreementY, leftAgreementR, leftAgreementZ,
    rightAgreementY, rightAgreementR, rightAgreementZ, mixedY, mixedR,
    mixedZ, errors, gap, movingNodes, strictRegularLayerGate, domainSize,
    targetAgreement, rowDegree, rightY, rightR, rightZ, leftY, leftR, leftZ]

/-!
## Conditional global cover interface

The two hypotheses that matter below are intentionally explicit:

* `hcover` must come from an upper first-exit classification into one terminal
  family and exactly `27` regular families;
* `hlayers` must come from an upper incidence proof retaining the fixed
  carrier's left-oriented agreement caps (or, in the fallback theorem, from
  an upper flag-trapezoid refinement).

Neither semantic fact follows from the arithmetic receipts in this file.
-/

/-- Arithmetic closure for the accepted proof's left-oriented cap. -/
theorem oriented_global_cover_receipt :
    terminalCap + regularLayerCount * orientedCap < challengeThreshold := by
  norm_num [terminalCap, regularLayerCount, orientedCap, orientedNumerator,
    orientedDot, pencilTerm, leftAgreementY, leftAgreementR, leftAgreementZ,
    mixedY, mixedR, mixedZ, errors, gap, movingNodes, challengeThreshold,
    domainSize, targetAgreement, rowDegree, rightY, rightR, rightZ, leftY,
    leftR, leftZ]

/-- Generic arithmetic handoff for a terminal family plus `27` uniformly
bounded regular families.  All mathematical content is supplied through the
cover and per-layer hypotheses. -/
theorem card_lt_challenge_of_uniform_layer_cover
    (card terminal layerCap : ℕ)
    (regular : Fin regularLayerCount → ℕ)
    (hterminal : terminal ≤ terminalCap)
    (hlayers : ∀ i, regular i ≤ layerCap)
    (hcover : card ≤ terminal + ∑ i, regular i)
    (harithmetic :
      terminalCap + regularLayerCount * layerCap < challengeThreshold) :
    card < challengeThreshold := by
  calc
    card ≤ terminal + ∑ i, regular i := hcover
    _ ≤ terminalCap + ∑ _i : Fin regularLayerCount, layerCap :=
      Nat.add_le_add hterminal (Finset.sum_le_sum fun i _ ↦ hlayers i)
    _ = terminalCap + regularLayerCount * layerCap := by
      unfold regularLayerCount
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
      simp
    _ < challengeThreshold := harithmetic

/-- Conditional global closure via the left-oriented proper-cut cap.

The missing upper theorem is precisely `hlayers`: each layer must retain the
same fixed carrier on the left of its proper-cut call.  The missing upper
classification is precisely `hcover`. -/
theorem card_lt_challenge_of_oriented_cover
    (card terminal : ℕ) (regular : Fin regularLayerCount → ℕ)
    (hterminal : terminal ≤ terminalCap)
    (hlayers : ∀ i, regular i ≤ orientedCap)
    (hcover : card ≤ terminal + ∑ i, regular i) :
    card < challengeThreshold :=
  card_lt_challenge_of_uniform_layer_cover card terminal orientedCap regular
    hterminal hlayers hcover oriented_global_cover_receipt

/-- The accepted flag-trapezoid arithmetic is an independent conditional
fallback: it also closes all `27` layers if an upper proof supplies the
refined per-layer cap. -/
theorem flag_global_cover_receipt :
    terminalCap + regularLayerCount * flagRefinedCap < challengeThreshold := by
  norm_num [terminalCap, regularLayerCount, flagRefinedCap,
    flagRefinedNumerator, symmetricNumerator, symmetricDot, pencilTerm,
    flagMixedZSaving, flagMixedZ, oneMixedZUnitSaving, symmetricAgreementY,
    symmetricAgreementR, symmetricAgreementZ, leftAgreementY,
    leftAgreementR, leftAgreementZ, rightAgreementY, rightAgreementR,
    rightAgreementZ, mixedY, mixedR, mixedZ, errors, gap, movingNodes,
    challengeThreshold, domainSize, targetAgreement, rowDegree, rightY,
    rightR, rightZ, leftY, leftR, leftZ]

theorem card_lt_challenge_of_flag_cover
    (card terminal : ℕ) (regular : Fin regularLayerCount → ℕ)
    (hterminal : terminal ≤ terminalCap)
    (hlayers : ∀ i, regular i ≤ flagRefinedCap)
    (hcover : card ≤ terminal + ∑ i, regular i) :
    card < challengeThreshold :=
  card_lt_challenge_of_uniform_layer_cover card terminal flagRefinedCap regular
    hterminal hlayers hcover flag_global_cover_receipt

#print axioms card_lt_layer_gate_of_oriented_incidence
#print axioms oriented_cap_lt_layer_gate
#print axioms minimal_mixedZ_saving_receipt
#print axioms flag_refined_cap_receipt
#print axioms card_lt_challenge_of_oriented_cover
#print axioms card_lt_challenge_of_flag_cover

end ProximityPrize.SubmissionUpper.OrientedMixedIncidenceGate
