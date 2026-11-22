import ProximityPrize.SubmissionLower.Low48BentLattice

-- merged module Low48BentCount
section Merged_Low48BentCount
set_option autoImplicit false

namespace Low48BentCount
open Finset
open Low48BentLattice
open K1_13_6_2_4 (Exponent)
open scoped BigOperators
open private slice slice_count evenSlice oddSlice sum_pair pairedSum paired_sum
  from ProximityPrize.SubmissionLower.Fast054
noncomputable section

private def Slices (a : Cap) :=
  Σ h : Fin (2 * a.2 + 1), Σ z : Fin (2 * a.1.t - 2 * h.val + 1),
    Σ y : Fin ((2 * a.1.j - 4 * h.val - 3 * z.val) / 2 + 1),
      Σ x : Fin (2 * a.1.j - 4 * h.val - 3 * z.val - 2 * y.val + 1),
        Fin (2 * a.1.b - h.val - (z.val + y.val + x.val) + 1)

private def slicesEquiv (a : Cap) (ha : Chamber a) : latticePoints a ≃ Slices a where
  toFun e := by
    have he := (coords a e.val).mp e.property
    have hb := he.1
    have hj := he.2.1
    have ht := he.2.2.1
    have hh := he.2.2.2
    let h : Fin (2 * a.2 + 1) := ⟨e.val 4, by omega⟩
    let z : Fin (2 * a.1.t - 2 * h.val + 1) := ⟨e.val 3, by dsimp [h]; omega⟩
    let y : Fin ((2 * a.1.j - 4 * h.val - 3 * z.val) / 2 + 1) :=
      ⟨e.val 2, by dsimp [h, z]; omega⟩
    let x : Fin (2 * a.1.j - 4 * h.val - 3 * z.val - 2 * y.val + 1) :=
      ⟨e.val 1, by dsimp [h, z, y]; omega⟩
    exact ⟨h, z, y, x, ⟨e.val 0, by dsimp [h, z, y, x]; omega⟩⟩
  invFun s := by
    rcases s with ⟨h, z, y, x, u⟩
    have hh := h.isLt
    have hz := z.isLt
    have hy := y.isLt
    have hx := x.isLt
    have hu := u.isLt
    have haB := ha.1
    have haJ := ha.2.1
    have haT := ha.2.2
    refine ⟨Finsupp.equivFunOnFinite.symm ![u.val, x.val, y.val, z.val, h.val], (coords a _).mpr ?_⟩
    change u.val + x.val + y.val + z.val + h.val ≤ 2 * a.1.b ∧
      x.val + 2 * y.val + 3 * z.val + 4 * h.val ≤ 2 * a.1.j ∧
      z.val + 2 * h.val ≤ 2 * a.1.t ∧ h.val ≤ 2 * a.2
    omega
  left_inv e := by
    apply Subtype.ext
    ext i
    fin_cases i <;> rfl
  right_inv s := by
    rcases s with ⟨⟨h, hh⟩, ⟨z, hz⟩, ⟨y, hy⟩, ⟨x, hx⟩, ⟨u, hu⟩⟩
    rfl

private theorem slice_even_raw (b j i : ℕ) (hi : 3 * i ≤ j) (hb : 2 * j ≤ b) :
    slice (2 * j - 3 * (2 * i)) (b - 2 * i) =
      evenSlice ((b : ℚ) / 2) j i := by
  have hW : 2 * j - 3 * (2 * i) = 2 * (j - 3 * i) := by omega
  have hC : 2 * i ≤ b := by omega
  rw [hW]
  simp only [slice, evenSlice, Nat.mul_div_cancel_left _ (by decide : 0 < 2),
    Nat.mul_mod_right, Nat.cast_zero, add_zero]
  push_cast [Nat.cast_sub hi, Nat.cast_sub hC]
  ring

private theorem slice_odd_raw (b j i : ℕ) (hi : 3 * i + 3 ≤ j) (hb : 2 * j ≤ b) :
    slice (2 * j - 3 * (2 * i + 1)) (b - (2 * i + 1)) =
      oddSlice ((b : ℚ) / 2) j i := by
  have hW : 3 * (2 * i + 1) ≤ 2 * j := by omega
  have hC : 2 * i + 1 ≤ b := by omega
  have hdiv : (2 * j - 3 * (2 * i + 1)) / 2 = j - (3 * i + 2) := by omega
  have hmod : (2 * j - 3 * (2 * i + 1)) % 2 = 1 := by omega
  simp only [slice, oddSlice, hdiv, hmod]
  push_cast [Nat.cast_sub hW, Nat.cast_sub hC, Nat.cast_sub (show 3 * i + 2 ≤ j by omega)]
  ring

def sliceFour (b j t : ℚ) : ℚ := pairedSum b j t + evenSlice b j t

private theorem sum_slice (b j t : ℕ) (hj : 3 * t ≤ j) (hb : 2 * j ≤ b) :
    (∑ z ∈ range (2 * t + 1), slice (2 * j - 3 * z) (b - z)) =
      sliceFour ((b : ℚ) / 2) j t := by
  rw [sliceFour, sum_range_succ, sum_pair, slice_even_raw _ _ _ hj hb, ← paired_sum]
  congr 1
  apply sum_congr rfl
  intro i hi
  have hi' := mem_range.mp hi
  rw [slice_even_raw _ _ _ (by omega) hb, slice_odd_raw _ _ _ (by omega) hb]
  rfl

theorem card_eq (a : Cap) (ha : Chamber a) :
    ((latticePoints a).ncard : ℚ) =
      ∑ h ∈ range (2 * a.2 + 1),
        sliceFour ((a.1.b : ℚ) - (h : ℚ) / 2) (a.1.j - 2 * (h : ℚ)) (a.1.t - (h : ℚ)) := by
  classical
  let : Fintype (Slices a) := by unfold Slices; infer_instance
  rw [← Nat.card_coe_set_eq, Nat.card_congr (slicesEquiv a ha), Nat.card_eq_fintype_card]
  unfold Slices
  simp only [Fintype.card_sigma, Fintype.card_fin, Nat.cast_sum]
  rw [Fin.sum_univ_eq_sum_range (fun h =>
    ∑ z : Fin (2 * a.1.t - 2 * h + 1),
    ∑ y : Fin ((2 * a.1.j - 4 * h - 3 * z.val) / 2 + 1),
    ∑ x : Fin (2 * a.1.j - 4 * h - 3 * z.val - 2 * y.val + 1),
      ((2 * a.1.b - h - (z.val + y.val + x.val) + 1 : ℕ) : ℚ))]
  apply sum_congr rfl
  intro h hh
  have hh' := mem_range.mp hh
  obtain ⟨hB, hJ, hT⟩ := ha
  have hT' : h ≤ a.1.t := by omega
  have hJ' : 2 * h ≤ a.1.j := by omega
  have hB' : h ≤ 2 * a.1.b := by omega
  have hTW : 2 * a.1.t - 2 * h = 2 * (a.1.t - h) := by omega
  have hJW : 2 * a.1.j - 4 * h = 2 * (a.1.j - 2 * h) := by omega
  rw [hTW, hJW]
  rw [Fin.sum_univ_eq_sum_range (fun z =>
    ∑ y : Fin ((2 * (a.1.j - 2 * h) - 3 * z) / 2 + 1),
    ∑ x : Fin (2 * (a.1.j - 2 * h) - 3 * z - 2 * y.val + 1),
      ((2 * a.1.b - h - (z + y.val + x.val) + 1 : ℕ) : ℚ))]
  calc
    _ = ∑ z ∈ range (2 * (a.1.t - h) + 1),
        slice (2 * (a.1.j - 2 * h) - 3 * z) (2 * a.1.b - h - z) := by
      apply sum_congr rfl
      intro z hz
      have hz' := mem_range.mp hz
      have hw : 2 * (a.1.j - 2 * h) - 3 * z ≤ 2 * a.1.b - h - z := by omega
      rw [← slice_count _ _ hw]
      rw [Fin.sum_univ_eq_sum_range (fun y =>
        ∑ x : Fin (2 * (a.1.j - 2 * h) - 3 * z - 2 * y + 1),
          ((2 * a.1.b - h - (z + y + x.val) + 1 : ℕ) : ℚ))]
      apply sum_congr rfl
      intro y _
      rw [Fin.sum_univ_eq_sum_range (fun x =>
        ((2 * a.1.b - h - (z + y + x) + 1 : ℕ) : ℚ))]
      simp only [Nat.sub_sub, Nat.add_assoc]
    _ = _ := by
      rw [sum_slice _ _ _ (by omega) (by omega)]
      push_cast [Nat.cast_sub hT', Nat.cast_sub hJ', Nat.cast_sub hB']
      congr 1
      ring

end
end Low48BentCount
end Merged_Low48BentCount

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

private def sumSlices (b j t n : ℚ) : ℚ :=
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

private theorem sumSlices_eval (b j t h n : ℚ) :
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