/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ProximityPrize.Benchmark.TargetUpper

/-!
# Four-sheet dictionary load bridge

After splitting the 256 roots into four translates of `mu_64`, a signed
selector trade has one of `3^4 = 81` local states at each base site.  The four
Fourier channels below are the discrete four-point transform of that state.
Their quadratic identity retains the exact ternary load which a scalar lattice
norm loses.

The final identity separates the cyclic product check into a base-site term
and a 64-valued sheet carry.  Together these are the local algebraic
obligations for an exact 81-state dynamic program.  This module does not assert
the missing central-shell count.

The positive-carrier identity below is the genuinely mixed refinement.  It
partitions the nine states of one antipodal ternary pair into three disjoint
types.  Conditional on the resulting type skeleton, the even and odd channels
factor with nonnegative coefficients; tensoring twice therefore separates all
81 four-sheet states without a signed spectral correction.
-/

namespace ProximityPrize.SubmissionUpper.FourSheetLoadBridge

variable {R : Type*} [CommRing R]

def channelA (x0 x1 x2 x3 : R) : R := x0 + x1 + x2 + x3
def channelD (x0 x1 x2 x3 : R) : R := x0 - x1 + x2 - x3

def channelC (i x0 x1 x2 x3 : R) : R :=
  x0 - x2 + i * (x1 - x3)

def channelE (i x0 x1 x2 x3 : R) : R :=
  x0 - x2 - i * (x1 - x3)

/-- Exact Plancherel identity for one four-sheet dictionary state. -/
theorem channel_energy (i x0 x1 x2 x3 : R) (hi : i ^ 2 = -1) :
    channelA x0 x1 x2 x3 ^ 2 + channelD x0 x1 x2 x3 ^ 2 +
        2 * channelC i x0 x1 x2 x3 * channelE i x0 x1 x2 x3 =
      4 * (x0 ^ 2 + x1 ^ 2 + x2 ^ 2 + x3 ^ 2) := by
  have hCE : channelC i x0 x1 x2 x3 * channelE i x0 x1 x2 x3 =
      (x0 - x2) ^ 2 - i ^ 2 * (x1 - x3) ^ 2 := by
    simp only [channelC, channelE]
    ring
  rw [show 2 * channelC i x0 x1 x2 x3 * channelE i x0 x1 x2 x3 =
      2 * (channelC i x0 x1 x2 x3 * channelE i x0 x1 x2 x3) by ring,
    hCE, hi]
  simp only [channelA, channelD]
  ring

/-- A ternary local coordinate contributes either zero or one to the squared
load. -/
theorem ternary_square (x : R) (hx : x = 0 ∨ x = 1 ∨ x = -1) :
    x ^ 2 = 0 ∨ x ^ 2 = 1 := by
  rcases hx with rfl | rfl | rfl
  · exact Or.inl (by simp)
  · exact Or.inr (by simp)
  · exact Or.inr (by simp)

/-- Split the exponent sum of a local state into its base index and sheet
carry.  This is valid in particular in `ZMod 256`. -/
theorem exponent_sheet_split (j : ℕ) (x0 x1 x2 x3 : R) :
    (j : R) * x0 + (j + 64 : ℕ) * x1 + (j + 128 : ℕ) * x2 +
        (j + 192 : ℕ) * x3 =
      (j : R) * channelA x0 x1 x2 x3 +
        64 * (x1 + 2 * x2 + 3 * x3) := by
  simp only [channelA, Nat.cast_add, Nat.cast_ofNat]
  ring

/-- Cancellation-free factorization of one weighted antipodal ternary pair.

The left side is the explicit sum over the nine choices
`(u,v) ∈ {-1,0,1}²`, grouped by `F (u+v) * G (u-v)`.  The three terms on
the right are respectively the repeated/equal carrier, the
opposite-or-zero carrier, and the singleton carrier.  Because this theorem
uses only semiring operations, every coefficient remains nonnegative. -/
theorem positive_antipodal_carrier
    {S : Type*} [CommSemiring S]
    (P N Fm2 Fm1 F0 F1 F2 Gm2 Gm1 G0 G1 G2 : S) :
    N ^ 2 * Fm2 * G0 +
          N * Fm1 * Gm1 + N * P * F0 * Gm2 +
          N * Fm1 * G1 + F0 * G0 + P * F1 * Gm1 +
          P * N * F0 * G2 + P * F1 * G1 + P ^ 2 * F2 * G0 =
      (N ^ 2 * Fm2 + P ^ 2 * F2) * G0 +
        F0 * (P * N * Gm2 + G0 + P * N * G2) +
        (N * Fm1 + P * F1) * (Gm1 + G1) := by
  ring

/-- Rewrite the local product exponent directly in the even channels `A,D`
and the two antipodal odd differences.  After global balance kills the sum of
`A`, this leaves a mod-128 even gate followed by one odd parity bit. -/
theorem exponent_even_odd_split (j : ℕ) (x0 x1 x2 x3 : R) :
    (j : R) * x0 + (j + 64 : ℕ) * x1 + (j + 128 : ℕ) * x2 +
        (j + 192 : ℕ) * x3 =
      (j + 96 : ℕ) * channelA x0 x1 x2 x3 -
        32 * channelD x0 x1 x2 x3 -
        64 * ((x0 - x2) + (x1 - x3)) := by
  simp only [channelA, channelD, Nat.cast_add, Nat.cast_ofNat]
  ring

theorem dictionary_size_receipt : 3 ^ 4 = 81 := by norm_num
theorem base_site_count_receipt : 256 / 4 = 64 := by norm_num

def selectorCount : ℕ :=
  1642763237966455131089379983394824266573028270959430944304016753768099919875

def baseFieldCardinality : ℕ := 2 ^ 31 - 2 ^ 24 + 1
def keySpaceCardinality : ℕ := 256 * baseFieldCardinality ^ 6
def challengeThreshold : ℕ := 274980728111395088

/-- Exact padded mass of the radius-`50,...,77` carrier strata whose even
side has at least `128*p^2` configurations and whose odd side has at least
`2*p^4`.  The Python audit derives this integer by a nonnegative recurrence;
the theorem below only records the exact threshold it must beat. -/
def residueEligibleCarrierMass : ℕ :=
  636878168549930732850903658924090991729387338666029254655297743984638786395140356123396874246219074943809639068014563688562741479619857477698112716800

/-- On the residue-eligible carrier strata, sixteen times the uniform
contribution is insufficient and seventeen times is sufficient.  Thus the
remaining affine-fibre theorem has no hidden asymptotic slack. -/
theorem residue_eligible_multiplier_window :
    16 * residueEligibleCarrierMass <
        keySpaceCardinality * selectorCount * (challengeThreshold - 1) ∧
      keySpaceCardinality * selectorCount * (challengeThreshold - 1) <
        17 * residueEligibleCarrierMass := by
  norm_num [residueEligibleCarrierMass, keySpaceCardinality,
    baseFieldCardinality, selectorCount, challengeThreshold]

end ProximityPrize.SubmissionUpper.FourSheetLoadBridge

#print axioms ProximityPrize.SubmissionUpper.FourSheetLoadBridge.channel_energy
#print axioms ProximityPrize.SubmissionUpper.FourSheetLoadBridge.positive_antipodal_carrier
#print axioms ProximityPrize.SubmissionUpper.FourSheetLoadBridge.exponent_sheet_split
#print axioms ProximityPrize.SubmissionUpper.FourSheetLoadBridge.exponent_even_odd_split
#print axioms ProximityPrize.SubmissionUpper.FourSheetLoadBridge.residue_eligible_multiplier_window
