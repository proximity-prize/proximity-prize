import ProximityPrize.SubmissionLower.BCHKSFactorYZQuadratic6400

/-!
# Factor-specific direct-identity closure at score 64.00

The selected factor's own additive `Y+Z` cap replaces the global interpolation
cap in both the transposed incidence count and the sparse-row budget.
-/

namespace ProximityPrize.SubmissionLower

open Polynomial
open RationalFunctions.HenselNumerators.ConcreteFiniteNumerators

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

/-- The factor-specific seed fibre creates at least 185,331 direct affine
identities. -/
theorem factorYZ_min_identity_incidence_numeric_6400
    (t D : ℕ) (hD : 0 < D) (hT : 144802557 * D < t) :
    (262144 - 76780 - 185330) * t >
      (262144 - 185330) * D := by
  norm_num at hT ⊢
  nlinarith

/-- Sparse-row budget for the lower part of the direct-identity interval. -/
theorem factorYZ_identity_budget_low_6400
    (t D z : ℕ) (hD : 0 < D) (hT : 144802557 * D < t)
    (hzlo : 185331 ≤ z) (hzhi : z ≤ 203330) :
    z * t + (262144 - z) * D <
      185364 * t + (18000 + 1) * (t - 76780) := by
  have htkeep : 76780 ≤ t := by nlinarith
  have hzt : z * t ≤ 203330 * t := Nat.mul_le_mul_right t hzhi
  have hcomp : 262144 - z ≤ 76813 := by omega
  have hcompD : (262144 - z) * D ≤ 76813 * D :=
    Nat.mul_le_mul_right D hcomp
  have hupper := Nat.add_le_add hzt hcompD
  have hstrict :
      203330 * t + 76813 * D <
        185364 * t + (18000 + 1) * (t - 76780) := by
    norm_num at hT ⊢
    omega
  exact hupper.trans_lt hstrict

/-- Sparse-row budget for the remainder of the direct-identity interval.
Choosing `b = z - 185343` leaves an exact coefficient margin of 22 rows. -/
theorem factorYZ_identity_budget_high_6400
    (t D z : ℕ) (hD : 0 < D) (hT : 144802557 * D < t)
    (hzlo : 203331 ≤ z) (hzhi : z ≤ 212478) :
    z * t + (262144 - z) * D <
      185364 * t + ((z - 185343) + 1) * (t - 76780) := by
  have htkeep : 76780 ≤ t := by nlinarith
  have hzsub : z - 185343 + 185343 = z := Nat.sub_add_cancel (by omega)
  have hcomp : 262144 - z ≤ 58813 := by omega
  have hcompD : (262144 - z) * D ≤ 58813 * D :=
    Nat.mul_le_mul_right D hcomp
  have hb : z - 185343 ≤ 27135 := by omega
  have hbterm : ((z - 185343) + 1) * 76780 ≤ 27136 * 76780 :=
    Nat.mul_le_mul_right 76780 (by omega)
  have hstrict :
      z * t + 58813 * D <
        185364 * t + ((z - 185343) + 1) * (t - 76780) := by
    norm_num at hT hbterm ⊢
    nlinarith [Nat.sub_add_cancel htkeep]
  exact (Nat.add_le_add_left hcompD (z * t)).trans_lt hstrict

/-- Every direct-identity locus from 185,331 through 212,478 forces the
score-64 pencil under the factor-specific seed bound. -/
theorem factorYZ_extended_identity_force_pencil_6400
    {I F : Type} [Fintype I] [DecidableEq I]
    [Field F] [DecidableEq F]
    (omega : I ↪ F)
    (T : Finset F) (A : F → Finset I) (G : I → F[X])
    (sect : F → F[X]) (U₀ U₁ : I → F) (D : ℕ)
    (hn : Fintype.card I = 262144)
    (hD : 0 < D)
    (hrow : ∀ z ∈ T, 185364 ≤ (A z).card)
    (hroot : ∀ z ∈ T, ∀ i ∈ A z, (G i).eval z = 0)
    (hGdegree : ∀ i, (G i).natDegree ≤ D)
    (hsectDegree : ∀ z ∈ T, (sect z).natDegree ≤ 131071)
    (hagreement : ∀ z ∈ T, ∀ i ∈ A z,
      (sect z).eval (omega i) = U₀ i + z * U₁ i)
    (hT : 144802557 * D < T.card)
    (hzlo : 185331 ≤ (Finset.univ.filter fun i : I ↦ G i = 0).card)
    (hzhi : (Finset.univ.filter fun i : I ↦ G i = 0).card ≤ 212478) :
    ∃ Good : Finset F, ∃ p₀ p₁ : F[X],
      Good ⊆ T ∧ 76780 < Good.card ∧
      p₀.natDegree ≤ 131071 ∧ p₁.natDegree ≤ 131071 ∧
      ∀ z ∈ Good, sect z = p₀ + Polynomial.C z * p₁ := by
  let Zero : Finset I := Finset.univ.filter fun i ↦ G i = 0
  have hkeep : 76780 ≤ T.card := by nlinarith
  have hzloZero : 185331 ≤ Zero.card := by simpa [Zero] using hzlo
  have hzhiZero : Zero.card ≤ 212478 := by simpa [Zero] using hzhi
  by_cases hlow : Zero.card ≤ 203330
  · apply sparse_identity_rows_force_pencil omega T A G sect U₀ U₁
      262144 185364 D 131071 18000 76780 hn hrow hroot
      hGdegree hsectDegree hagreement hkeep (by norm_num)
    · have hwide : 131071 + 3 * 18000 < Zero.card := by omega
      simpa [Zero] using hwide
    · simpa [Zero] using factorYZ_identity_budget_low_6400
        T.card D Zero.card hD hT (by simpa [Zero] using hzlo) hlow
  · have hhigh : 203331 ≤ Zero.card := by omega
    let b : ℕ := Zero.card - 185343
    have hbEq : b + 185343 = Zero.card := by
      dsimp [b]
      exact Nat.sub_add_cancel (by omega)
    have hwide : 131071 + 3 * b < Zero.card := by omega
    apply sparse_identity_rows_force_pencil omega T A G sect U₀ U₁
      262144 185364 D 131071 b 76780 hn hrow hroot
      hGdegree hsectDegree hagreement hkeep (by norm_num)
    · simpa [Zero] using hwide
    · simpa [Zero, b] using factorYZ_identity_budget_high_6400
        T.card D Zero.card hD hT hhigh (by simpa [Zero] using hzhi)

/-- A selected factor with at most 212,478 direct affine identities forces
the score-64 pencil, using only its own additive `Y+Z` cap. -/
theorem fixed_factor_low_identity_alignment_factorYZ6400
    {I F : Type} [Fintype I] [DecidableEq I]
    [Field F] [DecidableEq F]
    (omega : I ↪ F) (hn : Fintype.card I = 262144)
    (R : F[X][X][X]) (D : ℕ) (hD : 0 < D) (hYZ : YZCap R D)
    (T : Finset F) (P : F → F[X]) (A : F → Finset I)
    (U₀ U₁ : I → F)
    (hPdegree : ∀ z ∈ T, (P z).natDegree ≤ 131071)
    (hvan : ∀ z ∈ T, triEval R z (P z) = 0)
    (hrow : ∀ z ∈ T, 185364 ≤ (A z).card)
    (hagreement : ∀ z ∈ T, ∀ i ∈ A z,
      (P z).eval (omega i) = U₀ i + z * U₁ i)
    (hT : 144802557 * D < T.card)
    (hzhi : (Finset.univ.filter fun i : I ↦
      directAffineObstruction R (omega i) (U₀ i) (U₁ i) = 0).card ≤
        212478) :
    ∃ Good : Finset F, ∃ p₀ p₁ : F[X],
      Good ⊆ T ∧ 76780 < Good.card ∧
      p₀.natDegree ≤ 131071 ∧ p₁.natDegree ≤ 131071 ∧
      ∀ z ∈ Good, P z = p₀ + Polynomial.C z * p₁ := by
  classical
  let G : I → F[X] := fun i =>
    directAffineObstruction R (omega i) (U₀ i) (U₁ i)
  have hGdegree : ∀ i, (G i).natDegree ≤ D := by
    intro i
    exact directAffineObstruction_natDegree_le
      R (omega i) (U₀ i) (U₁ i) D hYZ
  have hGroot : ∀ z ∈ T, ∀ i ∈ A z, (G i).eval z = 0 := by
    intro z hz i hi
    exact directAffineObstruction_root_of_agreement R (P z)
      (omega i) (U₀ i) (U₁ i) z (hvan z hz) (hagreement z hz i hi)
  have hzlo : 185331 ≤
      (Finset.univ.filter fun i : I => G i = 0).card := by
    apply many_zero_obstructions_of_many_large_fibers
      T A G 262144 76780 185330 D hn
      (fun z hz ↦ by simpa using hrow z hz) hGroot hGdegree
    exact factorYZ_min_identity_incidence_numeric_6400
      T.card D hD hT
  apply factorYZ_extended_identity_force_pencil_6400
    omega T A G P U₀ U₁ D hn hD hrow hGroot hGdegree hPdegree
    hagreement hT hzlo
  simpa [G] using hzhi

end ProximityPrize.SubmissionLower
