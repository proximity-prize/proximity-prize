/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ProximityPrize.Benchmark.TargetUpper

/-!
# Carrier-rate transfer for square-free collision energies

If `D r` counts unordered disjoint equal-key trades in a radius cell, then
`2 * D r * choose (n - 2r) (k - r)` is that cell's ordered off-diagonal
energy at selector weight `k`.  This module isolates the exact linear
identity and a one- or two-source rate transfer.  The two-source statement is
the reusable integer form of a dual/LP certificate: any nonnegative integer
combination of two source carriers may be compared cellwise with the target.

For the 255-label moment key, Cauchy at weight 59 forces an off-diagonal mass
`L59`.  If radii below 55 absorb at most the exact budget recorded below, the
five remaining cells force enough weight-119 energy to cross the attack
threshold.  This improves the corresponding tolerance at weight 62 from
about 3.997 percent to more than 84.438 percent.  No lower-track module or
construction-specific collision claim is imported.

This is a conditional gate, not a standalone closure: the hypothesis that
radii below 55 fit the displayed budget remains construction-specific.  The
unrestricted Cauchy-source LP over weights `59,...,119` reaches only about
`0.24939690` of the target (with primal radius support at 37 and 117 and only
the weight-118 and weight-119 constraints binding), so Cauchy source rows by
themselves do not establish that hypothesis.
-/

namespace ProximityPrize.SubmissionUpper.CarrierRateTransfer

open scoped BigOperators

/-- Ordered off-diagonal energy carried by unordered trades in `cells`. -/
def carrierMass {I : Type*} [DecidableEq I] (cells : Finset I)
    (tradeCount carrier : I → ℕ) : ℕ :=
  ∑ i ∈ cells, 2 * tradeCount i * carrier i

/-- The exact algebraic identity for combining two carrier sources. -/
theorem two_source_carrier_identity
    {I : Type*} [DecidableEq I] (cells : Finset I)
    (tradeCount source₁ source₂ : I → ℕ) (weight₁ weight₂ : ℕ) :
    weight₁ * carrierMass cells tradeCount source₁ +
        weight₂ * carrierMass cells tradeCount source₂ =
      ∑ i ∈ cells,
        2 * tradeCount i * (weight₁ * source₁ i + weight₂ * source₂ i) := by
  simp only [carrierMass, Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- A cellwise two-source rate inequality sums to the corresponding global
carrier inequality.  All coefficients are integers, so this is directly
usable as an exact dual certificate. -/
theorem two_source_carrier_rate
    {I : Type*} [DecidableEq I] (cells : Finset I)
    (tradeCount source₁ source₂ target : I → ℕ)
    (weight₁ weight₂ numerator denominator : ℕ)
    (hrate : ∀ i ∈ cells,
      numerator * (weight₁ * source₁ i + weight₂ * source₂ i) ≤
        denominator * target i) :
    numerator *
        (weight₁ * carrierMass cells tradeCount source₁ +
          weight₂ * carrierMass cells tradeCount source₂) ≤
      denominator * carrierMass cells tradeCount target := by
  rw [two_source_carrier_identity, carrierMass, Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  calc
    numerator * (2 * tradeCount i *
        (weight₁ * source₁ i + weight₂ * source₂ i)) =
        2 * tradeCount i *
          (numerator * (weight₁ * source₁ i + weight₂ * source₂ i)) := by ring
    _ ≤ 2 * tradeCount i * (denominator * target i) :=
      Nat.mul_le_mul_left (2 * tradeCount i) (hrate i hi)
    _ = denominator * (2 * tradeCount i * target i) := by ring

/-- One-source specialization of `two_source_carrier_rate`. -/
theorem carrier_rate
    {I : Type*} [DecidableEq I] (cells : Finset I)
    (tradeCount source target : I → ℕ) (numerator denominator : ℕ)
    (hrate : ∀ i ∈ cells, numerator * source i ≤ denominator * target i) :
    numerator * carrierMass cells tradeCount source ≤
      denominator * carrierMass cells tradeCount target := by
  simpa using two_source_carrier_rate cells tradeCount source source target
    1 0 numerator denominator (by simpa using hrate)

/-- A generic cutoff theorem.  Cauchy supplies `sourceFloor`; cells below the
cutoff may consume `budget`, and the remaining cells transfer at a certified
local rate. -/
theorem carrier_transfer_after_budget
    {I : Type*} [DecidableEq I] (cells : Finset I)
    (tradeCount source target : I → ℕ)
    (sourceFloor lowMass budget goal numerator denominator : ℕ)
    (hdenominator : 0 < denominator)
    (hsource : sourceFloor ≤ lowMass + carrierMass cells tradeCount source)
    (hlow : lowMass ≤ budget)
    (hbudget : budget ≤ sourceFloor)
    (hrate : ∀ i ∈ cells, numerator * source i ≤ denominator * target i)
    (hgoal : denominator * goal ≤ numerator * (sourceFloor - budget)) :
    goal ≤ carrierMass cells tradeCount target := by
  have hresidual : sourceFloor - budget ≤ carrierMass cells tradeCount source := by
    omega
  have hscaled : denominator * goal ≤
      denominator * carrierMass cells tradeCount target := by
    calc
      denominator * goal ≤ numerator * (sourceFloor - budget) := hgoal
      _ ≤ numerator * carrierMass cells tradeCount source :=
        Nat.mul_le_mul_left numerator hresidual
      _ ≤ denominator * carrierMass cells tradeCount target :=
        carrier_rate cells tradeCount source target numerator denominator hrate
  exact Nat.le_of_mul_le_mul_left hscaled hdenominator

/-- Two independently lower-bounded sources can share one target carrier.
This is the reusable two-row LP/cutoff certificate. -/
theorem two_source_transfer_after_budgets
    {I : Type*} [DecidableEq I] (cells : Finset I)
    (tradeCount source₁ source₂ target : I → ℕ)
    (floor₁ floor₂ low₁ low₂ budget₁ budget₂ goal : ℕ)
    (weight₁ weight₂ numerator denominator : ℕ)
    (hdenominator : 0 < denominator)
    (hsource₁ : floor₁ ≤ low₁ + carrierMass cells tradeCount source₁)
    (hsource₂ : floor₂ ≤ low₂ + carrierMass cells tradeCount source₂)
    (hlow₁ : low₁ ≤ budget₁) (hlow₂ : low₂ ≤ budget₂)
    (hbudget₁ : budget₁ ≤ floor₁) (hbudget₂ : budget₂ ≤ floor₂)
    (hrate : ∀ i ∈ cells,
      numerator * (weight₁ * source₁ i + weight₂ * source₂ i) ≤
        denominator * target i)
    (hgoal : denominator * goal ≤
      numerator *
        (weight₁ * (floor₁ - budget₁) + weight₂ * (floor₂ - budget₂))) :
    goal ≤ carrierMass cells tradeCount target := by
  have hresidual₁ : floor₁ - budget₁ ≤ carrierMass cells tradeCount source₁ := by
    omega
  have hresidual₂ : floor₂ - budget₂ ≤ carrierMass cells tradeCount source₂ := by
    omega
  have hcombined :
      weight₁ * (floor₁ - budget₁) + weight₂ * (floor₂ - budget₂) ≤
        weight₁ * carrierMass cells tradeCount source₁ +
          weight₂ * carrierMass cells tradeCount source₂ :=
    Nat.add_le_add (Nat.mul_le_mul_left weight₁ hresidual₁)
      (Nat.mul_le_mul_left weight₂ hresidual₂)
  have hscaled : denominator * goal ≤
      denominator * carrierMass cells tradeCount target := by
    calc
      denominator * goal ≤ numerator *
          (weight₁ * (floor₁ - budget₁) +
            weight₂ * (floor₂ - budget₂)) := hgoal
      _ ≤ numerator *
          (weight₁ * carrierMass cells tradeCount source₁ +
            weight₂ * carrierMass cells tradeCount source₂) :=
        Nat.mul_le_mul_left numerator hcombined
      _ ≤ denominator * carrierMass cells tradeCount target :=
        two_source_carrier_rate cells tradeCount source₁ source₂ target
          weight₁ weight₂ numerator denominator hrate
  exact Nat.le_of_mul_le_mul_left hscaled hdenominator

def labelCount : ℕ := 255
def targetWeight : ℕ := 119
def sourceWeight59 : ℕ := 59
def cutoffRadius : ℕ := 55

def baseFieldCardinality : ℕ := 2 ^ 31 - 2 ^ 24 + 1
def keySpaceCardinality : ℕ := 256 * baseFieldCardinality ^ 6
def challengeThreshold : ℕ := 274980728111395088

def selectorCount119 : ℕ :=
  1642763237966455131089379983394824266573028270959430944304016753768099919875

def selectorCount59 : ℕ :=
  47561695200235528190994480101304699083038851332894189898375

def cauchyEnergy59 : ℕ :=
  94434999623569217943437683607251184096133543049958729501576

def forcedOffDiagonal59 : ℕ :=
  46873304423333689752443203505946485013094691717064539603201

def sourceCarrier59 (r : ℕ) : ℕ := Nat.choose (255 - 2 * r) (59 - r)
def targetCarrier119 (r : ℕ) : ℕ := Nat.choose (255 - 2 * r) (119 - r)

def sourceRate59 : ℕ := 17666220
def targetRate55 : ℕ := 1094093250378874652296508892509293208858350

def targetOffDiagonalGoal : ℕ := selectorCount119 * (challengeThreshold - 1)

def requiredHigh59 : ℕ :=
  7294012929362254523313334601655174354142232641934982820780

def lowRadiusBudget59 : ℕ :=
  39579291493971435229129868904291310658952459075129556782421

def roundingMargin59 : ℕ :=
  970073312641735798798440958886505580355500

set_option maxRecDepth 1000000 in
/-- Exact selector counts at the source and target weights. -/
theorem selector_count_receipts :
    selectorCount59 = Nat.choose 255 59 ∧
      selectorCount119 = Nat.choose 255 119 := by
  constructor <;> rw [Nat.choose_eq_fast_choose] <;> decide

/-- `cauchyEnergy59` is exactly the ceiling of `selectorCount59^2 / M`. -/
theorem cauchy_59_ceiling_receipt :
    keySpaceCardinality * (cauchyEnergy59 - 1) < selectorCount59 ^ 2 ∧
      selectorCount59 ^ 2 ≤ keySpaceCardinality * cauchyEnergy59 := by
  norm_num [keySpaceCardinality, baseFieldCardinality, cauchyEnergy59,
    selectorCount59]

/-- Exact off-diagonal Cauchy surplus at weight 59. -/
theorem forced_off_diagonal_59_receipt :
    forcedOffDiagonal59 = cauchyEnergy59 - selectorCount59 := by
  norm_num [forcedOffDiagonal59, cauchyEnergy59, selectorCount59]

set_option maxRecDepth 1000000 in
/-- Exact carrier values and cross-product margins for radii `55,...,59`. -/
theorem k59_carrier_rows_receipt :
    (sourceCarrier59 55, targetCarrier119 55,
      sourceRate59 * targetCarrier119 55 - targetRate55 * sourceCarrier59 55) =
        (17666220, 1094093250378874652296508892509293208858350, 0) ∧
    (sourceCarrier59 56, targetCarrier119 56,
      sourceRate59 * targetCarrier119 56 - targetRate55 * sourceCarrier59 56) =
        (477191, 271636944921651637811547035381617624268280,
          4276706576872235022735085092474038770572448606750) ∧
    (sourceCarrier59 57, targetCarrier119 57,
      sourceRate59 * targetCarrier119 57 - targetRate55 * sourceCarrier59 57) =
        (9870, 67420969290117416259735893741916321595200,
          1180274975711218608657904897972250234920122229500) ∧
    (sourceCarrier59 58, targetCarrier119 58,
      sourceRate59 * targetCarrier119 58 - targetRate55 * sourceCarrier59 58) =
        (139, 16728870698226702372856454283075285875040,
          295383831144623870416734935048691485075317838150) ∧
    (sourceCarrier59 59, targetCarrier119 59,
      sourceRate59 * targetCarrier119 59 - targetRate55 * sourceCarrier59 59) =
        (1, 4149513438753135746535867452761558241760,
          73305123208719042913514575802432786148536488850) := by
  norm_num [sourceCarrier59, targetCarrier119, sourceRate59, targetRate55,
    Nat.choose]

set_option maxRecDepth 1000000 in
/-- Every retained radius cell has at least the cutoff-55 target/source rate. -/
theorem k59_local_rate (r : ℕ) (hcutoff : 55 ≤ r) (hsource : r ≤ 59) :
    targetRate55 * sourceCarrier59 r ≤ sourceRate59 * targetCarrier119 r := by
  rcases k59_carrier_rows_receipt with ⟨h55, h56, h57, h58, h59⟩
  interval_cases r
  · rw [show sourceCarrier59 55 = 17666220 from congrArg Prod.fst h55,
      show targetCarrier119 55 =
        1094093250378874652296508892509293208858350 from
          congrArg (fun p ↦ p.2.1) h55]
    norm_num [sourceRate59, targetRate55]
  · rw [show sourceCarrier59 56 = 477191 from congrArg Prod.fst h56,
      show targetCarrier119 56 =
        271636944921651637811547035381617624268280 from
          congrArg (fun p ↦ p.2.1) h56]
    norm_num [sourceRate59, targetRate55]
  · rw [show sourceCarrier59 57 = 9870 from congrArg Prod.fst h57,
      show targetCarrier119 57 =
        67420969290117416259735893741916321595200 from
          congrArg (fun p ↦ p.2.1) h57]
    norm_num [sourceRate59, targetRate55]
  · rw [show sourceCarrier59 58 = 139 from congrArg Prod.fst h58,
      show targetCarrier119 58 =
        16728870698226702372856454283075285875040 from
          congrArg (fun p ↦ p.2.1) h58]
    norm_num [sourceRate59, targetRate55]
  · rw [show sourceCarrier59 59 = 1 from congrArg Prod.fst h59,
      show targetCarrier119 59 =
        4149513438753135746535867452761558241760 from
          congrArg (fun p ↦ p.2.1) h59]
    norm_num [sourceRate59, targetRate55]

/-- The residual requirement is the exact ceiling, including its remainder. -/
theorem required_high_59_receipt :
    targetRate55 * (requiredHigh59 - 1) <
        sourceRate59 * targetOffDiagonalGoal ∧
      sourceRate59 * targetOffDiagonalGoal ≤ targetRate55 * requiredHigh59 ∧
      targetRate55 * requiredHigh59 - sourceRate59 * targetOffDiagonalGoal =
        roundingMargin59 := by
  norm_num [targetRate55, requiredHigh59, sourceRate59,
    targetOffDiagonalGoal, selectorCount119, challengeThreshold,
    roundingMargin59]

/-- The exact cutoff-55 absorption budget and its certified 84.4388% window. -/
theorem low_radius_budget_59_receipt :
    lowRadiusBudget59 + requiredHigh59 = forcedOffDiagonal59 ∧
      844388762 * forcedOffDiagonal59 < 1000000000 * lowRadiusBudget59 ∧
      1000000000 * lowRadiusBudget59 < 844388763 * forcedOffDiagonal59 := by
  norm_num [lowRadiusBudget59, requiredHigh59, forcedOffDiagonal59]

/-- Concrete cutoff-55 transfer from the weight-59 Cauchy surplus. -/
theorem k59_cutoff_55_transfer
    (tradeCount : ℕ → ℕ) (lowSourceMass : ℕ)
    (hsource : forcedOffDiagonal59 ≤ lowSourceMass +
      carrierMass (Finset.Icc 55 59) tradeCount sourceCarrier59)
    (hlow : lowSourceMass ≤ lowRadiusBudget59) :
    targetOffDiagonalGoal ≤
      carrierMass (Finset.Icc 55 59) tradeCount targetCarrier119 := by
  apply carrier_transfer_after_budget (Finset.Icc 55 59) tradeCount
    sourceCarrier59 targetCarrier119 forcedOffDiagonal59 lowSourceMass
    lowRadiusBudget59 targetOffDiagonalGoal targetRate55 sourceRate59
  · norm_num [sourceRate59]
  · exact hsource
  · exact hlow
  · norm_num [lowRadiusBudget59, forcedOffDiagonal59]
  · intro r hr
    exact k59_local_rate r (Finset.mem_Icc.mp hr).1 (Finset.mem_Icc.mp hr).2
  · norm_num [sourceRate59, targetRate55, targetOffDiagonalGoal,
      selectorCount119, challengeThreshold, forcedOffDiagonal59,
      lowRadiusBudget59]

/-- Adding the diagonal converts the transferred surplus into the exact
weight-119 collision-energy target. -/
theorem k59_target_energy
    (tradeCount : ℕ → ℕ) (lowSourceMass : ℕ)
    (hsource : forcedOffDiagonal59 ≤ lowSourceMass +
      carrierMass (Finset.Icc 55 59) tradeCount sourceCarrier59)
    (hlow : lowSourceMass ≤ lowRadiusBudget59) :
    selectorCount119 * challengeThreshold ≤ selectorCount119 +
      carrierMass (Finset.Icc 55 59) tradeCount targetCarrier119 := by
  have htransfer := k59_cutoff_55_transfer tradeCount lowSourceMass hsource hlow
  calc
    selectorCount119 * challengeThreshold =
        selectorCount119 + targetOffDiagonalGoal := by
      norm_num [targetOffDiagonalGoal, challengeThreshold]
      ring
    _ ≤ selectorCount119 +
        carrierMass (Finset.Icc 55 59) tradeCount targetCarrier119 :=
      Nat.add_le_add_left htransfer selectorCount119

/- The former k=62 cell remains as an exact comparison receipt. -/

def selectorCount62 : ℕ :=
  1554092852843655764882791079312277129371701525652141247821625

def cauchyEnergy62 : ℕ :=
  100825935081024018886941263431720829108914207554768283177760084

def forcedOffDiagonal62 : ℕ :=
  99271842228180363122058472352408551979542506029116141929938459

def requiredHigh62 : ℕ :=
  95303572935047217601612029905226508111222411699522485536299896

def lowRadiusBudget62 : ℕ :=
  3968269293133145520446442447182043868320094329593656393638563

theorem k62_comparison_receipt :
    keySpaceCardinality * (cauchyEnergy62 - 1) < selectorCount62 ^ 2 ∧
      selectorCount62 ^ 2 ≤ keySpaceCardinality * cauchyEnergy62 ∧
      forcedOffDiagonal62 = cauchyEnergy62 - selectorCount62 ∧
      lowRadiusBudget62 + requiredHigh62 = forcedOffDiagonal62 ∧
      39973765 * forcedOffDiagonal62 < 1000000000 * lowRadiusBudget62 ∧
      1000000000 * lowRadiusBudget62 < 39973766 * forcedOffDiagonal62 := by
  norm_num [keySpaceCardinality, baseFieldCardinality, cauchyEnergy62,
    selectorCount62, forcedOffDiagonal62, lowRadiusBudget62, requiredHigh62]

end ProximityPrize.SubmissionUpper.CarrierRateTransfer

#print axioms ProximityPrize.SubmissionUpper.CarrierRateTransfer.two_source_carrier_identity
#print axioms ProximityPrize.SubmissionUpper.CarrierRateTransfer.two_source_carrier_rate
#print axioms ProximityPrize.SubmissionUpper.CarrierRateTransfer.carrier_transfer_after_budget
#print axioms ProximityPrize.SubmissionUpper.CarrierRateTransfer.two_source_transfer_after_budgets
#print axioms ProximityPrize.SubmissionUpper.CarrierRateTransfer.k59_cutoff_55_transfer
#print axioms ProximityPrize.SubmissionUpper.CarrierRateTransfer.k59_target_energy
