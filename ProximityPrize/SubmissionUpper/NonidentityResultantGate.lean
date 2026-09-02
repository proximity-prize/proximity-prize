/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ProximityPrize.Benchmark.TargetUpper

/-!
# Nonidentity resultant and irregular-carrier gates

The accepted lower `67.77` argument eliminates a carrier that is linear in its residual `R`
coordinate.  On a regular irreducible component, a coordinate whose resultant is not divisible
by the carrier pays the bidegree intersection cost

`fY * (bZ + bR * gZ) + fZ * (bY + bR * gY)`.

This file substitutes the complete accepted `67.77` degree box at the first score-improving upper
agreement.  Even assigning every factor the full box gives a per-coordinate cap
`879650019607790`, whereas sharp incidence requires `18274985104318683`.  After the affine
identity charge is restored, the whole regular chart is still more than twenty times below the
challenge threshold.

The two ordinary irregular strata are also recorded.  For a reduced positive-`Y` carrier, the
intersection with its `Y` derivative costs at most `(2*jY-1)*jZ`.  For an irreducible carrier
linear in `R`, simultaneous vanishing of its leading and constant coefficients costs at most
`2*jY*jZ`.  These are bidegree-Bezout inputs; the generic theorem below deliberately takes their
combined point bound as a hypothesis instead of importing the lower proof.

Finally, an injective extension-field chart cannot amplify either point bound.  The canonical
linear-`R` chart contains the actual challenge as one projected coordinate, and Frobenius twists
are still injective.  A genuinely noninjective trace/norm replacement is outside this closure: it
must have projection multiplicity at least `21` in the regular branch, or `61462789` in a purely
singular branch.  At any physical coordinate with nonzero received slope, the affine fixed center
still separates all actual challenges.

This is a research gate, not an upper score certificate.
-/

namespace ProximityPrize.SubmissionUpper.NonidentityResultantGate

/-! ## Generic counting and extension-chart facts -/

section Generic

variable {Seed Node : Type*}

/-- Double counting after all common/identity coordinates have been removed. -/
theorem card_mul_required_le_of_bounded_fibres
    (relation : Seed → Node → Prop)
    [∀ seed node, Decidable (relation seed node)]
    (seeds : Finset Seed) (nodes : Finset Node) (required fibreCap : ℕ)
    (hrequired : ∀ seed ∈ seeds,
      required ≤ (nodes.filter (relation seed)).card)
    (hfibre : ∀ node ∈ nodes,
      (seeds.filter fun seed ↦ relation seed node).card ≤ fibreCap) :
    seeds.card * required ≤ nodes.card * fibreCap := by
  calc
    seeds.card * required = ∑ _seed ∈ seeds, required := by simp
    _ ≤ ∑ seed ∈ seeds, (nodes.filter (relation seed)).card :=
      Finset.sum_le_sum hrequired
    _ = ∑ node ∈ nodes,
        (seeds.filter fun seed ↦ relation seed node).card := by
      simp_rw [Finset.card_eq_sum_ones, Finset.sum_filter]
      rw [Finset.sum_comm]
    _ ≤ ∑ _node ∈ nodes, fibreCap := Finset.sum_le_sum hfibre
    _ = nodes.card * fibreCap := by simp

variable {Point : Type*} [DecidableEq Point]

/-- An injective extension-field chart transports a point-count cap without any field-size
multiplier.  This is the precise reason that merely moving the challenge to an extension does not
enlarge the accepted linear-`R` nonidentity fibre. -/
theorem challenge_card_le_of_injective_point_chart
    (point : Seed → Point) (seeds : Finset Seed) (allowed : Finset Point)
    (hinjective : Function.Injective point)
    (hallowed : ∀ seed ∈ seeds, point seed ∈ allowed) :
    seeds.card ≤ allowed.card := by
  calc
    seeds.card = (seeds.image point).card :=
      (Finset.card_image_of_injective seeds hinjective).symm
    _ ≤ allowed.card := by
      apply Finset.card_le_card
      intro p hp
      obtain ⟨seed, hseed, rfl⟩ := Finset.mem_image.mp hp
      exact hallowed seed hseed

variable {F : Type*} [Field F]

/-- A fixed-center coordinate with nonzero second-row slope separates actual challenges, even if
some auxiliary trace, norm, or selector key identifies them. -/
theorem affine_fixed_center_injective (u₀ u₁ : F) (hu₁ : u₁ ≠ 0) :
    Function.Injective (fun gamma : F ↦ u₀ + gamma * u₁) := by
  intro gamma eta heq
  have hmul : (gamma - eta) * u₁ = 0 := by
    linear_combination heq
  exact sub_eq_zero.mp ((mul_eq_zero.mp hmul).resolve_right hu₁)

end Generic

/-! ## Accepted-box arithmetic at the first upper improvement -/

def fieldCharacteristic : ℕ := 2130706433
def extensionDegree : ℕ := 6
def domainSize : ℕ := 262144
def rowDegree : ℕ := 131071
def targetAgreement : ℕ := 139782
def targetErrors : ℕ := domainSize - targetAgreement
def agreementGap : ℕ := targetAgreement - rowDegree
def movingCoordinates : ℕ := domainSize - rowDegree
def challengeThreshold : ℕ := 274980728111395088

/-- Accepted `67.77` residual degree box. -/
def boxY : ℕ := 4925
def boxZ : ℕ := 227115

/-- Coordinate degrees of the agreement polynomial in `(Y,R,Z)`. -/
def agreementY : ℕ := 1 + 2 * rowDegree * boxY
def agreementR : ℕ := rowDegree
def agreementZ : ℕ := 2 * rowDegree * boxZ + 1

/-- Bidegree intersection cost after eliminating a carrier linear in `R`. -/
def resultantFibreCost (fY fZ gY gZ : ℕ) : ℕ :=
  fY * (agreementZ + agreementR * gZ) +
    fZ * (agreementY + agreementR * gY)

def maximumResultantFibre : ℕ := 879650019607790

/-- Least per-coordinate cap not rejected by sharp incidence. -/
def minimumRequiredFibre : ℕ := 18274985104318683

/-- The identity-resultant alternative is charged once per possible positive-`Y` factor degree. -/
def identityNumerator : ℕ :=
  (targetErrors + 1) * agreementGap * boxY

def regularIdentityCap : ℕ := 13235951356862532

/-- Bezout point charge for `f = ∂f/∂Y = 0` in the reduced positive-`Y` carrier. -/
def ySingularPointCap : ℕ := (2 * boxY - 1) * boxZ

/-- Bezout point charge for simultaneous vanishing of the two coefficients of a linear-`R`
irreducible carrier. -/
def rSingularPointCap : ℕ := 2 * boxY * boxZ

def combinedSingularPointCap : ℕ := ySingularPointCap + rSingularPointCap
def fullReducedChartCap : ℕ := regularIdentityCap + combinedSingularPointCap

/-- First projection multiplicity that can evade the regular per-coordinate fibre gate. -/
def minimumRegularProjectionMultiplicity : ℕ := 21

/-- First projection multiplicity that can make a purely singular point set threshold-sized. -/
def minimumSingularProjectionMultiplicity : ℕ := 61462789

theorem accepted_box_receipt :
    targetErrors = 122362 ∧ agreementGap = 8711 ∧
      movingCoordinates = 131073 ∧
      agreementY = 1291049351 ∧ agreementR = 131071 ∧
      agreementZ = 59536380331 := by
  norm_num [targetErrors, agreementGap, movingCoordinates, agreementY,
    agreementR, agreementZ, targetAgreement, domainSize, rowDegree, boxY,
    boxZ]

/-- Monotonicity of the resultant cost over the complete accepted box. -/
theorem resultantFibreCost_le_maximum
    (fY fZ gY gZ : ℕ)
    (hfY : fY ≤ boxY) (hfZ : fZ ≤ boxZ)
    (hgY : gY ≤ boxY) (hgZ : gZ ≤ boxZ) :
    resultantFibreCost fY fZ gY gZ ≤ maximumResultantFibre := by
  calc
    resultantFibreCost fY fZ gY gZ ≤
        boxY * (agreementZ + agreementR * boxZ) +
          boxZ * (agreementY + agreementR * boxY) := by
      apply Nat.add_le_add
      · exact Nat.mul_le_mul hfY
          (Nat.add_le_add_left (Nat.mul_le_mul_left agreementR hgZ) agreementZ)
      · exact Nat.mul_le_mul hfZ
          (Nat.add_le_add_left (Nat.mul_le_mul_left agreementR hgY) agreementY)
    _ = maximumResultantFibre := by
      norm_num [maximumResultantFibre, agreementY, agreementR, agreementZ,
        rowDegree, boxY, boxZ]

theorem nonidentity_fibre_boundary :
    movingCoordinates * maximumResultantFibre <
        challengeThreshold * agreementGap ∧
      movingCoordinates * (minimumRequiredFibre - 1) <
        challengeThreshold * agreementGap ∧
      challengeThreshold * agreementGap ≤
        movingCoordinates * minimumRequiredFibre := by
  norm_num [movingCoordinates, maximumResultantFibre, minimumRequiredFibre,
    challengeThreshold, agreementGap, targetAgreement, rowDegree, domainSize]

/-- Even after adding every affine-identity charge, the regular accepted box is small. -/
theorem regular_identity_cap_receipt :
    movingCoordinates * maximumResultantFibre + identityNumerator =
        regularIdentityCap * agreementGap + 443 ∧
      regularIdentityCap < challengeThreshold := by
  norm_num [movingCoordinates, maximumResultantFibre, identityNumerator,
    regularIdentityCap, agreementGap, targetErrors, targetAgreement,
    challengeThreshold, boxY, domainSize, rowDegree]

theorem singular_strata_receipt :
    ySingularPointCap = 2236855635 ∧
      rSingularPointCap = 2237082750 ∧
      combinedSingularPointCap = 4473938385 ∧
      fullReducedChartCap = 13235955830800917 ∧
      fullReducedChartCap < challengeThreshold := by
  norm_num [ySingularPointCap, rSingularPointCap,
    combinedSingularPointCap, fullReducedChartCap, regularIdentityCap,
    boxY, boxZ, challengeThreshold]

/-- Conditional closure of every regular/nonidentity component in the accepted box, including
the complete factor-aggregated affine-identity charge. -/
theorem regular_identity_card_lt_threshold
    (card cost : ℕ) (hcost : cost ≤ maximumResultantFibre)
    (hincidence : card * agreementGap ≤
      movingCoordinates * cost + identityNumerator) :
    card < challengeThreshold := by
  norm_num [maximumResultantFibre, agreementGap, movingCoordinates,
    identityNumerator, targetErrors, targetAgreement, domainSize, rowDegree,
    boxY, challengeThreshold] at hcost hincidence ⊢
  omega

/-- Conditional closure after adding both reduced irreducible singular strata.  The algebraic
input is exactly the combined Bezout point cap documented above. -/
theorem full_reduced_linearR_chart_lt_threshold
    (card regularOrIdentity singular : ℕ)
    (hregular : regularOrIdentity * agreementGap ≤
      movingCoordinates * maximumResultantFibre + identityNumerator)
    (hsingular : singular ≤ combinedSingularPointCap)
    (hcover : card ≤ regularOrIdentity + singular) :
    card < challengeThreshold := by
  norm_num [agreementGap, movingCoordinates, maximumResultantFibre,
    identityNumerator, targetErrors, targetAgreement, domainSize, rowDegree,
    boxY, combinedSingularPointCap, ySingularPointCap, rSingularPointCap,
    boxZ, challengeThreshold] at hregular hsingular hcover ⊢
  omega

/-- A noninjective replacement needs at least twenty-one challenges over one resultant point
before the accepted box can even meet the sharp regular incidence boundary. -/
theorem regular_projection_multiplicity_boundary :
    maximumResultantFibre * (minimumRegularProjectionMultiplicity - 1) <
        minimumRequiredFibre ∧
      minimumRequiredFibre ≤
        maximumResultantFibre * minimumRegularProjectionMultiplicity := by
  norm_num [maximumResultantFibre, minimumRegularProjectionMultiplicity,
    minimumRequiredFibre]

/-- Purely singular concentration needs more than sixty-one million challenges over one projected
point.  The canonical challenge-containing chart has multiplicity one. -/
theorem singular_projection_multiplicity_boundary :
    combinedSingularPointCap * (minimumSingularProjectionMultiplicity - 1) <
        challengeThreshold ∧
      challengeThreshold ≤
        combinedSingularPointCap * minimumSingularProjectionMultiplicity := by
  norm_num [combinedSingularPointCap, ySingularPointCap,
    rSingularPointCap, minimumSingularProjectionMultiplicity,
    challengeThreshold, boxY, boxZ]

#print axioms card_mul_required_le_of_bounded_fibres
#print axioms challenge_card_le_of_injective_point_chart
#print axioms affine_fixed_center_injective
#print axioms resultantFibreCost_le_maximum
#print axioms regular_identity_card_lt_threshold
#print axioms full_reduced_linearR_chart_lt_threshold
#print axioms regular_projection_multiplicity_boundary
#print axioms singular_projection_multiplicity_boundary

end ProximityPrize.SubmissionUpper.NonidentityResultantGate
