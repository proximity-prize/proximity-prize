/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ProximityPrize.Benchmark.TargetUpper

/-!
# Factorized-locator codimension and extension-challenge gates

The accepted lower construction can project a high band, divide by a forced
factor, and repeat.  On the upper side, a fixed agreement factor does not
reduce the interpolation codimension: matching that factor consumes exactly
the row-space dimension removed from the remaining interpolation problem.
At the benchmark target the cost is always

`139782 - 131072 = 8710`,

independently of the fixed factor degree.  One affine challenge coordinate
leaves `8709` syndrome conditions, whereas the all-locator entropy permits at
most `8430` base-field pins while retaining the required challenge count.

The second gate concerns the order-two-invariant `1024`-fibre proposal.  Its
two surviving moments are base-field coefficients.  At any high coefficient
where the fixed challenge direction is nonzero, an affine coefficient
identity

`a + gamma * b = iota(moment)`

confines `gamma` to one affine copy of the base field.  That gives at most
`2130706433` challenges, far below the required
`274980728111395088`.  Thus a large image of moment pairs in a product slice
does not by itself let those two pins become one scalar affine challenge.

Finally, multiplying the two-coordinate outer high tail in degrees `130` and
`128` by a nonzero polynomial does not pack it modulo the legal degree-`127`
space.  The two shifted copies retain distinct triangular leading pivots.
These are template gates for a fixed affine received-word line, not a global
obstruction to non-collinear syndrome-line attacks.

For the smaller reciprocal family, a selector-dependent normalisation
`gamma * rho(L) = -1` is genuinely nonlinear and therefore is not covered by
the fixed-line theorem verbatim.  If a reciprocity-preserving twist uses a
quadratic parameter `theta` outside the base field, however, every residual
equation `iota(a) + theta * iota(b) = 0` splits into the two base equations
`a = b = 0`.  The companion exact audit checks that the canonical
parity-matched palindromic twists do not make all these equations automatic.
It does not claim an upper bound on their exceptional selector zero sets.
-/

namespace ProximityPrize.SubmissionUpper.FactorizedLocatorCodimensionGate

open Polynomial

def benchmarkAgreement : ℕ := 139782
def rowDimension : ℕ := 131072
def supportCodimension : ℕ := benchmarkAgreement - rowDimension
def residualAfterAffineScalar : ℕ := supportCodimension - 1
def allLocatorDensityPinCap : ℕ := 8430

def baseFieldCardinality : ℕ := 2130706433
def challengeThreshold : ℕ := 274980728111395088
def antipodalSelectorCount : ℕ :=
  8759284249504283281529408629099087875
def reciprocalSelectorCount : ℕ := 759510004936100355

/-- The target support has interpolation codimension `8710`. -/
theorem support_codimension_receipt : supportCodimension = 8710 := by
  norm_num [supportCodimension, benchmarkAgreement, rowDimension]

/-- A single affine scalar leaves the `8709`-coordinate high band. -/
theorem residual_after_affine_scalar_receipt : residualAfterAffineScalar = 8709 := by
  norm_num [residualAfterAffineScalar, supportCodimension,
    benchmarkAgreement, rowDimension]

/-- Fixing any agreement factor first leaves the total interpolation
codimension unchanged.  The first summand is the cost of matching a factor
larger than the row space; the second is the residual interpolation cost.
This covers both sides of the breakpoint `f = 131072`. -/
theorem fixed_factor_codimension_conservation (f : ℕ)
    (hf : f ≤ benchmarkAgreement) :
    (f - rowDimension) +
        ((benchmarkAgreement - f) - (rowDimension - f)) = supportCodimension := by
  norm_num [benchmarkAgreement, rowDimension, supportCodimension] at hf ⊢
  omega

/-- Even after granting one affine scalar, a threshold-sized family would
need `279` further automatic conditions relative to the exact integer pin
cap found by the companion all-locator entropy audit. -/
theorem threshold_condition_savings_receipt :
    residualAfterAffineScalar - allLocatorDensityPinCap = 279 := by
  norm_num [residualAfterAffineScalar, supportCodimension,
    benchmarkAgreement, rowDimension, allLocatorDensityPinCap]

/-- A quadratic-extension value space is large enough in cardinality.  The
obstruction below is therefore affine-line compatibility, not raw capacity. -/
theorem quadratic_extension_capacity_receipt :
    challengeThreshold < baseFieldCardinality ^ 2 := by
  norm_num [challengeThreshold, baseFieldCardinality]

/-- One affine copy of the base field is far too small for the winning-set
threshold. -/
theorem base_field_capacity_too_small :
    baseFieldCardinality < challengeThreshold := by
  norm_num [baseFieldCardinality, challengeThreshold]

/-- The antipodal selector pool has enough records even after a crude
`128`-state product pigeonhole.  This deliberately says nothing about the
image of its two-moment map. -/
theorem antipodal_product_slice_raw_capacity :
    128 * challengeThreshold < antipodalSelectorCount := by
  norm_num [challengeThreshold, antipodalSelectorCount]

/-- The full reciprocal selector pool is only between two and three winning
thresholds.  Thus an exceptional construction would have to retain more than
one third of all `34`-of-`63` selectors; a merely nonempty zero set is not
enough. -/
theorem reciprocal_pool_narrow_margin :
    2 * challengeThreshold < reciprocalSelectorCount ∧
      reciprocalSelectorCount < 3 * challengeThreshold := by
  norm_num [challengeThreshold, reciprocalSelectorCount]

section AffineCoefficient

variable {K F U : Type*} [Field K] [Field F] [Fintype K] [DecidableEq F]

/-- If one nonzero coefficient of a fixed affine challenge direction must
cancel a base-field moment, all resulting challenges lie in an affine copy
of the base field. -/
theorem challenge_image_card_le_base
    (ι : K →+* F) (S : Finset U) (moment : U → K) (challenge : U → F)
    (a b : F) (hb : b ≠ 0)
    (hcoeff : ∀ u ∈ S, a + challenge u * b = ι (moment u)) :
    (S.image challenge).card ≤ Fintype.card K := by
  classical
  let scaled : K → F := fun x ↦ (ι x - a) / b
  have hsubset : S.image challenge ⊆
      (Finset.univ : Finset K).image scaled := by
    intro gamma hgamma
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hgamma
    apply Finset.mem_image.mpr
    refine ⟨moment u, Finset.mem_univ _, ?_⟩
    dsimp only [scaled]
    symm
    apply (eq_div_iff hb).2
    linear_combination hcoeff u hu
  calc
    (S.image challenge).card ≤
        ((Finset.univ : Finset K).image scaled).card :=
      Finset.card_le_card hsubset
    _ ≤ (Finset.univ : Finset K).card := Finset.card_image_le
    _ = Fintype.card K := Finset.card_univ

/-- Benchmark specialization: a scalar used at any nonzero high coefficient
cannot yield enough challenges, even before imposing the far/message
functional. -/
theorem challenge_image_lt_threshold
    (ι : K →+* F) (S : Finset U) (moment : U → K) (challenge : U → F)
    (a b : F) (hb : b ≠ 0)
    (hcoeff : ∀ u ∈ S, a + challenge u * b = ι (moment u))
    (hcard : Fintype.card K = baseFieldCardinality) :
    (S.image challenge).card < challengeThreshold := by
  exact (challenge_image_card_le_base ι S moment challenge a b hb hcoeff).trans_lt <| by
    rw [hcard]
    exact base_field_capacity_too_small

/-- The same cardinality cap survives a selector-dependent inverse
normalisation when the pivot depends on only one base-field moment.  The map
`x ↦ -(a + iota(x) * b)⁻¹` still has a domain of size `|K|`; it need not be
affine. -/
theorem inverse_affine_image_card_le_base
    (ι : K →+* F) (S : Finset U) (moment : U → K) (challenge : U → F)
    (a b : F)
    (hnormalize : ∀ u ∈ S,
      challenge u * (a + ι (moment u) * b) = -1) :
    (S.image challenge).card ≤ Fintype.card K := by
  classical
  let normalized : K → F := fun x ↦ -(a + ι x * b)⁻¹
  have hsubset : S.image challenge ⊆
      (Finset.univ : Finset K).image normalized := by
    intro gamma hgamma
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hgamma
    apply Finset.mem_image.mpr
    refine ⟨moment u, Finset.mem_univ _, ?_⟩
    dsimp only [normalized]
    have hpivot : a + ι (moment u) * b ≠ 0 := by
      intro hpivot
      have hbad := hnormalize u hu
      rw [hpivot, mul_zero] at hbad
      exact (zero_ne_one : (0 : F) ≠ 1) (neg_eq_zero.mp hbad.symm).symm
    apply (mul_right_cancel₀ hpivot)
    rw [hnormalize u hu]
    simp [hpivot]
  calc
    (S.image challenge).card ≤
        ((Finset.univ : Finset K).image normalized).card :=
      Finset.card_le_card hsubset
    _ ≤ (Finset.univ : Finset K).card := Finset.card_image_le
    _ = Fintype.card K := Finset.card_univ

end AffineCoefficient

section NonlinearExtensionNormalization

variable {K F : Type*} [Field K] [Field F]

/-- An affine equation in a genuinely non-base extension parameter is two
base-field equations.  This is the precise replacement for the fixed-line
cardinality obstruction when the challenge is normalised nonlinearly as the
inverse of a selector-dependent pivot. -/
theorem nonbase_affine_eq_zero_iff
    (ι : K →+* F) (θ : F) (hθ : θ ∉ Set.range ι) (a b : K) :
    ι a + θ * ι b = 0 ↔ a = 0 ∧ b = 0 := by
  constructor
  · intro h
    have hb : b = 0 := by
      by_contra hb
      have hιb : ι b ≠ 0 := (_root_.map_ne_zero ι).2 hb
      have hθeq : θ = ι (-a / b) := by
        rw [_root_.map_div₀ ι, _root_.map_neg ι]
        apply (eq_div_iff hιb).2
        linear_combination h
      exact hθ ⟨-a / b, hθeq.symm⟩
    have ha : a = 0 := by
      apply ι.injective
      simpa [hb] using h
    exact ⟨ha, hb⟩
  · rintro ⟨rfl, rfl⟩
    simp

/-- In particular, translating a genuinely non-base parameter by one base
element can never give zero.  This is the obstruction met by the second high
coefficient of the top palindromic complement truncation: its `theta`
component is the degree-two coefficient of `L * R = G`, namely `1`. -/
theorem nonbase_translate_ne_zero
    (ι : K →+* F) (θ : F) (hθ : θ ∉ Set.range ι) (a : K) :
    ι a + θ ≠ 0 := by
  intro h
  have hθeq : θ = ι (-a) := by
    rw [_root_.map_neg ι]
    linear_combination h
  exact hθ ⟨-a, hθeq.symm⟩

end NonlinearExtensionNormalization

section PolynomialTwist

variable {F : Type*} [Field F]

/-- A polynomial twist cannot identify the degree-`130` tail direction with
the degree-`128` direction modulo polynomials of legal outer degree at most
`127`.  Their distinct leading pivots survive every nonzero twist. -/
theorem twist_tail_not_proportional_mod_low
    (M : Polynomial F) (hM : M ≠ 0) (c : F) (P : Polynomial F)
    (hP : P.natDegree ≤ M.natDegree + 127) :
    M * Polynomial.X ^ 130 ≠
      Polynomial.C c * (M * Polynomial.X ^ 128) + P := by
  have hX130 : (Polynomial.X : Polynomial F) ^ 130 ≠ 0 :=
    pow_ne_zero _ Polynomial.X_ne_zero
  have hX128 : (Polynomial.X : Polynomial F) ^ 128 ≠ 0 :=
    pow_ne_zero _ Polynomial.X_ne_zero
  have hleft : (M * Polynomial.X ^ 130).natDegree = M.natDegree + 130 := by
    rw [Polynomial.natDegree_mul hM hX130, Polynomial.natDegree_X_pow]
  have hrightTerm :
      (Polynomial.C c * (M * Polynomial.X ^ 128)).natDegree ≤
        M.natDegree + 128 := by
    calc
      (Polynomial.C c * (M * Polynomial.X ^ 128)).natDegree ≤
          (Polynomial.C c).natDegree + (M * Polynomial.X ^ 128).natDegree :=
        Polynomial.natDegree_mul_le
      _ = M.natDegree + 128 := by
        rw [Polynomial.natDegree_C,
          Polynomial.natDegree_mul hM hX128, Polynomial.natDegree_X_pow]
        omega
  have hright :
      (Polynomial.C c * (M * Polynomial.X ^ 128) + P).natDegree ≤
        M.natDegree + 128 := by
    exact (Polynomial.natDegree_add_le _ _).trans <| max_le hrightTerm <| by
      omega
  intro heq
  have hdegrees := congrArg Polynomial.natDegree heq
  rw [hleft] at hdegrees
  omega

end PolynomialTwist

#print axioms fixed_factor_codimension_conservation
#print axioms challenge_image_card_le_base
#print axioms challenge_image_lt_threshold
#print axioms inverse_affine_image_card_le_base
#print axioms nonbase_affine_eq_zero_iff
#print axioms nonbase_translate_ne_zero
#print axioms twist_tail_not_proportional_mod_low

end ProximityPrize.SubmissionUpper.FactorizedLocatorCodimensionGate
