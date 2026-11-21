import ProximityPrize.SubmissionLower.Low48BentCount

set_option autoImplicit false

namespace Low48BentVolume
open Finset Polynomial MvPolynomial
open Low48BentLattice
open Low48BentCount (sliceFour)
open K1_13_6 (GeoField)
open K1_13_6_2 (GeoJets5)
open K1_13_6_2_4_3 (monomial_hilbert_count)
open private pairedSum pair evenSlice oddSlice from ProximityPrize.SubmissionLower.Fast054
open scoped BigOperators Pointwise
noncomputable section

def sumSlices (b j t n : ℚ) : ℚ :=
  let f : ℚ → ℚ := fun h => sliceFour (b - h / 2) (j - 2 * h) (t - h)
  n * f 0 + n * (n - 1) / 2 * (f 1 - f 0) +
    n * (n - 1) * (n - 2) / 6 * (f 2 - 2 * f 1 + f 0) +
    n * (n - 1) * (n - 2) * (n - 3) / 24 * (f 3 - 3 * f 2 + 3 * f 1 - f 0) +
    n * (n - 1) * (n - 2) * (n - 3) * (n - 4) / 120 *
      (f 4 - 4 * f 3 + 6 * f 2 - 4 * f 1 + f 0)

private theorem sum_slices (b j t : ℚ) (n : ℕ) :
    (∑ h ∈ range n, sliceFour (b - (h : ℚ) / 2) (j - 2 * (h : ℚ)) (t - (h : ℚ))) =
      sumSlices b j t n := by
  induction n with
  | zero => simp [sumSlices]
  | succ n ih =>
    rw [sum_range_succ, ih]
    push_cast
    unfold sumSlices sliceFour pairedSum pair evenSlice oddSlice
    ring

private def coeff1 (b j t h : ℚ) : ℚ :=
  2 * b
    + j
    - (1 / 2) * t
    - (1 / 15) * h

private def coeff2 (b j t h : ℚ) : ℚ :=
  4 * b * j
    - b * t
    - j ^ 2
    + 2 * j * t
    - (1 / 6) * j * h
    - (5 / 2) * t ^ 2
    + (4 / 3) * t * h
    - h ^ 2

private def coeff3 (b j t h : ℚ) : ℚ :=
  2 * b * j ^ 2
    + 2 * b * j * t
    - (2 / 3) * b * j * h
    - 3 * b * t ^ 2
    + (4 / 3) * b * t * h
    - j ^ 3
    + (3 / 2) * j ^ 2 * t
    + (1 / 2) * j ^ 2 * h
    - (11 / 2) * j * t ^ 2
    + (22 / 3) * j * t * h
    - 9 * j * h ^ 2
    + (13 / 2) * t ^ 3
    - (35 / 3) * t ^ 2 * h
    + 8 * t * h ^ 2
    + (20 / 3) * h ^ 3

private def coeff4 (b j t h : ℚ) : ℚ :=
  4 * b * j ^ 2 * t
    - 12 * b * j * t ^ 2
    + 12 * b * j * t * h
    - 12 * b * j * h ^ 2
    + 12 * b * t ^ 3
    - 18 * b * t ^ 2 * h
    + 12 * b * t * h ^ 2
    + 8 * b * h ^ 3
    - 2 * j ^ 3 * t
    + 7 * j ^ 2 * t ^ 2
    - j ^ 2 * t * h
    + j ^ 2 * h ^ 2
    - 10 * j * t ^ 3
    - 3 * j * t ^ 2 * h
    + 4 * j * t * h ^ 2
    - (4 / 3) * j * h ^ 3
    + (9 / 2) * t ^ 4
    + 9 * t ^ 3 * h
    - 12 * t ^ 2 * h ^ 2
    + (20 / 3) * t * h ^ 3
    - 4 * h ^ 4

private def coeff5 (b j t h : ℚ) : ℚ :=
  8 * b * j ^ 2 * t * h
    - 8 * b * j ^ 2 * h ^ 2
    - 24 * b * j * t ^ 2 * h
    + 16 * b * j * t * h ^ 2
    + (32 / 3) * b * j * h ^ 3
    + 24 * b * t ^ 3 * h
    - 24 * b * t ^ 2 * h ^ 2
    + (32 / 3) * b * t * h ^ 3
    - 16 * b * h ^ 4
    - 4 * j ^ 3 * t * h
    + 4 * j ^ 3 * h ^ 2
    + 14 * j ^ 2 * t ^ 2 * h
    - 8 * j ^ 2 * t * h ^ 2
    - 8 * j ^ 2 * h ^ 3
    - 20 * j * t ^ 3 * h
    + 16 * j * t ^ 2 * h ^ 2
    - (16 / 3) * j * t * h ^ 3
    + 16 * j * h ^ 4
    + 9 * t ^ 4 * h
    - 8 * t ^ 3 * h ^ 2
    + (8 / 3) * t ^ 2 * h ^ 3
    - (48 / 5) * h ^ 5

def bentIntegral (b j t h : ℚ) : ℚ := 60 * coeff5 b j t h

theorem sumSlices_eval (b j t h n : ℚ) :
    sumSlices (n * b) (n * j) (n * t) (2 * n * h + 1) =
      coeff5 b j t h * n^5 + coeff4 b j t h * n^4 +
        coeff3 b j t h * n^3 + coeff2 b j t h * n^2 + coeff1 b j t h * n + 1 := by
  unfold sumSlices sliceFour pairedSum pair evenSlice oddSlice coeff1 coeff2 coeff3 coeff4 coeff5
  ring

private def latticePolynomial (a : Cap) : ℚ[X] :=
  let b : ℚ := a.1.b
  let j : ℚ := a.1.j
  let t : ℚ := a.1.t
  let h : ℚ := a.2
  Polynomial.C (coeff5 b j t h) * Polynomial.X ^ 5 +
    Polynomial.C (coeff4 b j t h) * Polynomial.X ^ 4 +
    Polynomial.C (coeff3 b j t h) * Polynomial.X ^ 3 +
    Polynomial.C (coeff2 b j t h) * Polynomial.X ^ 2 +
    Polynomial.C (coeff1 b j t h) * Polynomial.X ^ 1 + Polynomial.C 1

private theorem latticePolynomial_eval (a : Cap) (ha : Chamber a) (n : ℕ) :
    (latticePolynomial a).eval (n : ℚ) = ((latticePoints (Scale n a)).ncard : ℚ) := by
  rw [Low48BentCount.card_eq (Scale n a) (chamber_scale ha n), sum_slices]
  simp only [latticePolynomial, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_C, Polynomial.eval_X, pow_one, Scale, K1_13.Shape.scale]
  push_cast
  simpa only [mul_assoc] using (sumSlices_eval a.1.b a.1.j a.1.t a.2 n).symm

theorem ambient_coeff (a : Cap) (ha : Chamber a) :
    (affineHilbertPolynomial
      ((⊥ : Ideal GeoJets5).comap (monomialMap GeoField (latticePoints a)).toRingHom)).coeff 5 =
      bentIntegral a.1.b a.1.j a.1.t a.2 / 60 := by
  let I := (⊥ : Ideal GeoJets5).comap (monomialMap GeoField (latticePoints a)).toRingHom
  have hP : affineHilbertPolynomial I = latticePolynomial a := by
    apply Polynomial.eq_of_eventually_atTop_eval_natCast_eq
    filter_upwards [eventually_eval_affineHilbertPolynomial I] with n hn
    rw [hn, latticePolynomial_eval a ha n, ← lattice_scale a ha n]
    exact_mod_cast monomial_hilbert_count (latticePoints a) (zero_mem a) n
  change (affineHilbertPolynomial I).coeff 5 = _
  rw [hP]
  simp only [latticePolynomial, Polynomial.coeff_add, Polynomial.coeff_C_mul_X_pow,
    Polynomial.coeff_C]
  norm_num [bentIntegral]

end
end Low48BentVolume
