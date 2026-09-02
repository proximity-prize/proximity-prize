/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ProximityPrize.Benchmark.TargetUpper

/-!
# Exact symmetry receipts for the 1024-fibre square key

The proposed square-jet selector key records the moments with exponents
`-1, 1, 2, 3, 4, 5` and the product residue in `ZMod 256`.  Three tempting
ways to obtain the missing factor `4.009...` are product-character energy,
subgroup-invariant selectors, and very small antipodal trades.  The exact
receipts below show that none supplies it:

* the complete nontrivial product-character energy is less than `10^-76`
  times the trivial Fourier energy;
* antipodal selectors miss the challenge threshold by a factor between
  `18.242` and `18.243`, with the order-four and order-eight families much
  smaller; and
* the concrete four-pair key has `10,334,625` inputs.  The companion exact
  audit exhausts those inputs and finds the key `(e1,e2,e4)` injective.

The last computational fact is deliberately exposed through a conditional
consumer rather than asserted as a Lean axiom.  It is checked independently by
`scripts/upper-square-key-symmetry-audit.py`.
-/

namespace ProximityPrize.SubmissionUpper.SquareKeySymmetryGate

open scoped BigOperators

def selectorCount : ℕ :=
  1642763237966455131089379983394824266573028270959430944304016753768099919875

def baseFieldCardinality : ℕ := 2 ^ 31 - 2 ^ 24 + 1
def challengeThreshold : ℕ := 274980728111395088

/-! ## Product-coordinate Fourier receipts -/

/-- Orders of the nontrivial characters of `ZMod 256`. -/
def nontrivialProductCharacterOrders : Finset ℕ := {2, 4, 8, 16, 32, 64, 128, 256}

/-- Absolute value of the weight-136 elementary Fourier coefficient, indexed
by the character order.  For even `q` this is
`choose (256 / q - 1) (136 / q)`; order one is the trivial coefficient. -/
def productFourierMagnitude : ℕ → ℕ
  | 1 => selectorCount
  | 2 => 8759284249504283281529408629099087875
  | 4 => 759510004936100355
  | 8 => 265182525
  | 16 => 6435
  | 32 => 35
  | 64 => 3
  | 128 => 1
  | 256 => 1
  | _ => 0

set_option maxRecDepth 1000000 in
theorem product_fourier_magnitude_receipt :
    productFourierMagnitude 1 = Nat.choose 255 136 ∧
      productFourierMagnitude 2 = Nat.choose 127 68 ∧
      productFourierMagnitude 4 = Nat.choose 63 34 ∧
      productFourierMagnitude 8 = Nat.choose 31 17 ∧
      productFourierMagnitude 16 = Nat.choose 15 8 ∧
      productFourierMagnitude 32 = Nat.choose 7 4 ∧
      productFourierMagnitude 64 = Nat.choose 3 2 ∧
      productFourierMagnitude 128 = Nat.choose 1 1 ∧
      productFourierMagnitude 256 = Nat.choose 0 0 := by
  norm_num [productFourierMagnitude, selectorCount, Nat.choose]

/-- Sum of the squared nontrivial product coefficients, with `phi(q)=q/2`
characters of each order `q`. -/
def nontrivialProductEnergy : ℕ :=
  ∑ q ∈ nontrivialProductCharacterOrders,
    (q / 2) * productFourierMagnitude q ^ 2

theorem nontrivial_product_energy_receipt :
    nontrivialProductEnergy =
      76725060563613815211123464898334715770886346357185281714634025672827064055 := by
  norm_num [nontrivialProductEnergy, nontrivialProductCharacterOrders,
    productFourierMagnitude]

/-- Product imbalance is over 76 decimal orders too small to provide the
required order-one Fourier correction. -/
theorem product_energy_negligible :
    10 ^ 76 * nontrivialProductEnergy < selectorCount ^ 2 := by
  norm_num [nontrivialProductEnergy, nontrivialProductCharacterOrders,
    productFourierMagnitude, selectorCount]

/-! ## Invariant selector families -/

def antipodalSelectorCount : ℕ := 8759284249504283281529408629099087875
def antipodalKeySpace : ℕ := 128 * baseFieldCardinality ^ 2

def orderFourSelectorCount : ℕ := 759510004936100355
def orderFourKeySpace : ℕ := 64 * baseFieldCardinality

def orderEightSelectorCount : ℕ := 265182525
def orderEightKeySpace : ℕ := 32

set_option maxRecDepth 1000000 in
theorem invariant_selector_count_receipts :
    antipodalSelectorCount = Nat.choose 127 68 ∧
      orderFourSelectorCount = Nat.choose 63 34 ∧
      orderEightSelectorCount = Nat.choose 31 17 := by
  norm_num [antipodalSelectorCount, orderFourSelectorCount, orderEightSelectorCount,
    Nat.choose]

/-- Exact rational form of the `18.242772...` antipodal deficit. -/
theorem antipodal_deficit_window :
    18242 * antipodalSelectorCount <
        1000 * challengeThreshold * antipodalKeySpace ∧
      1000 * challengeThreshold * antipodalKeySpace <
        18243 * antipodalSelectorCount := by
  norm_num [antipodalSelectorCount, antipodalKeySpace, baseFieldCardinality,
    challengeThreshold]

/-- The order-four invariant family misses by `49,371,048,389.000...`. -/
theorem order_four_deficit_window :
    49371048389 * orderFourSelectorCount <
        challengeThreshold * orderFourKeySpace ∧
      challengeThreshold * orderFourKeySpace <
        49371048390 * orderFourSelectorCount := by
  norm_num [orderFourSelectorCount, orderFourKeySpace, baseFieldCardinality,
    challengeThreshold]

/-- The order-eight invariant family misses by `33,182,364,861.955...`. -/
theorem order_eight_deficit_window :
    33182364861 * orderEightSelectorCount <
        challengeThreshold * orderEightKeySpace ∧
      challengeThreshold * orderEightKeySpace <
        33182364862 * orderEightSelectorCount := by
  norm_num [orderEightSelectorCount, orderEightKeySpace, challengeThreshold]

/-! ## Concrete antipodal quartet key -/

def modulus : ℕ := 2130706433
def primitiveRoot256 : ℕ := 392596362
def primitiveRoot128 : ℕ := primitiveRoot256 ^ 2 % modulus

def antipodalRoot (j : Fin 127) : ℕ :=
  primitiveRoot128 ^ (j.val + 1) % modulus

def elementaryOne (U : Finset (Fin 127)) : ℕ :=
  (∑ j ∈ U, antipodalRoot j) % modulus

def elementaryTwo (U : Finset (Fin 127)) : ℕ :=
  (∑ pair ∈ U.powersetCard 2, ∏ j ∈ pair, antipodalRoot j) % modulus

def elementaryFour (U : Finset (Fin 127)) : ℕ :=
  (∏ j ∈ U, antipodalRoot j) % modulus

/-- The two even moments determine `e1,e2`; the exact product gives `e4`. -/
def antipodalQuartetKey (U : Finset (Fin 127)) : ℕ × ℕ × ℕ :=
  (elementaryOne U, elementaryTwo U, elementaryFour U)

def antipodalQuartets : Finset (Finset (Fin 127)) :=
  Finset.univ.powersetCard 4

set_option maxRecDepth 1000000 in
theorem antipodal_quartet_count_receipt : antipodalQuartets.card = 10334625 := by
  rw [antipodalQuartets, Finset.card_powersetCard, Finset.card_univ]
  norm_num [Nat.choose]

/-- Trusted consumer for the exhaustive external injectivity certificate.  No
computational claim is smuggled into Lean: callers must supply injectivity of
the concrete key on the quartet family. -/
theorem quartet_fibre_card_le_one
    (hInjective : Set.InjOn antipodalQuartetKey (antipodalQuartets : Set _))
    (key : ℕ × ℕ × ℕ) :
    (antipodalQuartets.filter fun U ↦ antipodalQuartetKey U = key).card ≤ 1 := by
  rw [Finset.card_le_one_iff]
  intro A B hA hB
  simp only [Finset.mem_filter] at hA hB
  exact hInjective hA.1 hB.1 (hA.2.trans hB.2.symm)

end ProximityPrize.SubmissionUpper.SquareKeySymmetryGate

#print axioms ProximityPrize.SubmissionUpper.SquareKeySymmetryGate.product_energy_negligible
#print axioms ProximityPrize.SubmissionUpper.SquareKeySymmetryGate.antipodal_deficit_window
#print axioms ProximityPrize.SubmissionUpper.SquareKeySymmetryGate.quartet_fibre_card_le_one
