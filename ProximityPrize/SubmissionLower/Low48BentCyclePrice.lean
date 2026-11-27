import ProximityPrize.SubmissionLower.Low48BentSupport
import ProximityPrize.SubmissionLower.Low48BentCycleCap

set_option Elab.async false

-- merged module Low48BentCount
section Merged_Low48BentCount

set_option autoImplicit false

namespace Low48BentCount
open Finset
open Low48BentLattice
open K1_13_6_2_4 (Exponent)
open scoped BigOperators
open K1_13_6_2_3_1 (slice slice_count evenSlice oddSlice sum_pair pairedSum paired_sum)
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

-- merged module Low48BentVolume
section Merged_Low48BentVolume

set_option autoImplicit false

namespace Low48BentVolume
open Finset Polynomial MvPolynomial
open Low48BentLattice
open Low48BentCount (sliceFour)
open K1_13_6 (GeoField)
open K1_13_6_2 (GeoJets5)
open K1_13_6_2_4_3 (monomial_hilbert_count)
open K1_13_6_2_3_1 (pairedSum pair evenSlice oddSlice)
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

def coeff5 (b j t h : ℚ) : ℚ :=
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

def latticePolynomial (a : Cap) : (Polynomial ℚ) :=
  let b : ℚ := a.1.b
  let j : ℚ := a.1.j
  let t : ℚ := a.1.t
  let h : ℚ := a.2
  Polynomial.C (coeff5 b j t h) * Polynomial.X ^ 5 +
    Polynomial.C (coeff4 b j t h) * Polynomial.X ^ 4 +
    Polynomial.C (coeff3 b j t h) * Polynomial.X ^ 3 +
    Polynomial.C (coeff2 b j t h) * Polynomial.X ^ 2 +
    Polynomial.C (coeff1 b j t h) * Polynomial.X ^ 1 + Polynomial.C 1

theorem latticePolynomial_eval (a : Cap) (ha : Chamber a) (n : ℕ) :
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

end Merged_Low48BentVolume

-- merged module Low48BentVolumePrice
section Merged_Low48BentVolumePrice

set_option autoImplicit false

namespace Low48BentVolume
open Low48BentVolume (coeff5)
theorem cast_price_integral (a : Low48BentLattice.Cap) :
    (Low48Price.bentIntegral a.1.b a.1.j a.1.t a.2 : ℚ) =
      bentIntegral a.1.b a.1.j a.1.t a.2 := by
  unfold Low48Price.bentIntegral bentIntegral coeff5
  push_cast
  ring
end Low48BentVolume

end Merged_Low48BentVolumePrice

-- merged module Low48BentPolarization
section Merged_Low48BentPolarization

set_option autoImplicit false
set_option maxHeartbeats 650000

namespace Low48BentPolarization
open Finset MvPolynomial
open Low48BentLattice
open K1_13 (Shape)
open K1_13_6_2_4_1
  (Grade Form line line_coeff squarefree squarefree_apply squarefree_degree
   cube_extract positiveDiagonal positiveDiagonal_apply)
open scoped BigOperators
noncomputable section

private def zeroDiagonal (s : Finset (Fin 5)) (i : Fin 5) : ℚ := if i ∈ s then 1 else 0

private theorem zero_cube_prod (a : Grade) :
    (∑ J ∈ (univ : Finset (Fin 5)).powerset, (-1 : ℚ) ^ (5 - J.card) *
      ∏ j ∈ (univ : Finset (Fin 5)) \ J, (0 : ℚ) ^ a j) =
      ∏ j : Fin 5, ((1 : ℚ) - (0 : ℚ) ^ a j) := by
  classical
  rw [Finset.prod_sub (fun _ => (1 : ℚ)) (fun j => (0 : ℚ) ^ a j)]
  refine Finset.sum_bij (fun J _ => univ \ J) ?_ ?_ ?_ ?_
  · intro J _
    simp
  · intro J _ K _ h
    simpa using congrArg (fun U : Finset (Fin 5) => univ \ U) h
  · intro J _
    exact ⟨univ \ J, by simp, by simp⟩
  · intro J _
    simp [Finset.card_sdiff_of_subset (Finset.subset_univ J)]

private theorem zero_cube_monomial (a : Grade) (r : ℚ) :
    (∑ J ∈ (univ : Finset (Fin 5)).powerset, (-1 : ℚ) ^ (5 - J.card) *
      eval (zeroDiagonal J) (monomial a r)) =
      r * ∏ j : Fin 5, ((1 : ℚ) - (0 : ℚ) ^ a j) := by
  rw [← zero_cube_prod, Finset.mul_sum]
  refine sum_congr rfl fun J _ => ?_
  rw [eval_monomial, Finsupp.prod_pow]
  have hv (j : Fin 5) : zeroDiagonal J j ^ a j =
      if j ∈ (univ : Finset (Fin 5)) \ J then (0 : ℚ) ^ a j else 1 := by
    by_cases hj : j ∈ J <;> simp [zeroDiagonal, hj]
  simp_rw [hv]
  rw [Finset.prod_ite_mem, Finset.univ_inter]
  ring

private theorem zero_cube_monomial_top {a : Grade} (ha : a.degree = 5) (r : ℚ) :
    (∑ J ∈ (univ : Finset (Fin 5)).powerset, (-1 : ℚ) ^ (5 - J.card) *
      eval (zeroDiagonal J) (monomial a r)) =
      (monomial a r).coeff (squarefree univ) := by
  classical
  rw [zero_cube_monomial]
  by_cases h : squarefree (univ : Finset (Fin 5)) ≤ a
  · have he : squarefree (univ : Finset (Fin 5)) = a := by
      obtain ⟨b, hab⟩ := le_iff_exists_add.mp h
      have hd := congrArg Finsupp.degree hab
      rw [ha, map_add, squarefree_degree, card_univ, Fintype.card_fin] at hd
      have hb : b.degree = 0 := by omega
      rw [hab, (Finsupp.degree_eq_zero_iff _).mp hb, add_zero]
    subst a
    simp [squarefree_apply]
  · obtain ⟨j, hj⟩ := not_forall.mp h
    have hm : a j = 0 := by simpa [squarefree_apply] using hj
    rw [Finset.prod_eq_zero (mem_univ j) (by simp [hm]), mul_zero, coeff_monomial]
    exact (ite_eq_right (fun he => h he.ge)).symm

private theorem zero_cube (p : Form) :
    (∑ J ∈ (univ : Finset (Fin 5)).powerset, (-1 : ℚ) ^ (5 - J.card) *
      eval (zeroDiagonal J) (homogeneousComponent 5 p)) =
      p.coeff (squarefree univ) := by
  classical
  induction p using MvPolynomial.induction_on' with
  | monomial a r =>
    simp only [homogeneousComponent_of_mem (isHomogeneous_monomial r rfl)]
    by_cases h : 5 = a.degree
    · simpa only [ite_eq_left h] using zero_cube_monomial_top h.symm r
    · have hne : a ≠ squarefree univ := fun h' => h (by rw [h', squarefree_degree]; simp)
      simp [h, coeff_monomial, hne]
  | add p q hp hq =>
    simp only [map_add, mul_add, Finset.sum_add_distrib]
    exact congrArg₂ (· + ·) hp hq

private def bend {R : Type*} [CommRing R] (b j t h : R) : R :=
  -576 * h ^ 5 + 160 * t ^ 2 * h ^ 3 - 480 * t ^ 3 * h ^ 2 + 540 * t ^ 4 * h
  + 960 * j * h ^ 4 - 320 * j * t * h ^ 3 + 960 * j * t ^ 2 * h ^ 2 - 1200 * j * t ^ 3 * h
  - 480 * j ^ 2 * h ^ 3 - 480 * j ^ 2 * t * h ^ 2 + 840 * j ^ 2 * t ^ 2 * h
  + 240 * j ^ 3 * h ^ 2 - 240 * j ^ 3 * t * h - 960 * b * h ^ 4 + 640 * b * t * h ^ 3
  - 1440 * b * t ^ 2 * h ^ 2 + 1440 * b * t ^ 3 * h + 640 * b * j * h ^ 3
  + 960 * b * j * t * h ^ 2 - 1440 * b * j * t ^ 2 * h - 480 * b * j ^ 2 * h ^ 2
  + 480 * b * j ^ 2 * t * h

private def linear (caps : Fin 5 → Cap) (f : Cap → ℕ) : Form :=
  ∑ i : Fin 5, MvPolynomial.C (f (caps i) : ℚ) * MvPolynomial.X i

private theorem linear_homogeneous (caps : Fin 5 → Cap) (f : Cap → ℕ) :
    (linear caps f).IsHomogeneous 1 := by
  apply IsHomogeneous.sum
  intro i _
  exact isHomogeneous_C_mul_X _ _

private def form (caps : Fin 5 → Cap) : Form :=
  bend (linear caps fun p => p.1.b) (linear caps fun p => p.1.j)
    (linear caps fun p => p.1.t) (linear caps Prod.snd)

private theorem nat_homogeneous (n : ℕ) : IsHomogeneous (n : Form) 0 := by
  simpa using (isHomogeneous_C (σ:=Fin 5) (n : ℚ))

private theorem form_homogeneous (caps : Fin 5 → Cap) : (form caps).IsHomogeneous 5 := by
  unfold form bend
  generalize hb : linear caps (fun a => a.1.b) = b
  generalize hj : linear caps (fun a => a.1.j) = j
  generalize ht : linear caps (fun a => a.1.t) = t
  generalize hh : linear caps Prod.snd = h
  have hb' : b.IsHomogeneous 1 := hb ▸ linear_homogeneous caps _
  have hj' : j.IsHomogeneous 1 := hj ▸ linear_homogeneous caps _
  have ht' : t.IsHomogeneous 1 := ht ▸ linear_homogeneous caps _
  have hh' : h.IsHomogeneous 1 := hh ▸ linear_homogeneous caps _
  have m0 := ((nat_homogeneous 576).neg).mul (hh'.pow 5)
  have m1 := (((nat_homogeneous 160)).mul (ht'.pow 2)).mul (hh'.pow 3)
  have m2 := (((nat_homogeneous 480)).mul (ht'.pow 3)).mul (hh'.pow 2)
  have m3 := (((nat_homogeneous 540)).mul (ht'.pow 4)).mul hh'
  have m4 := (((nat_homogeneous 960)).mul hj').mul (hh'.pow 4)
  have m5 := ((((nat_homogeneous 320)).mul hj').mul ht').mul (hh'.pow 3)
  have m6 := ((((nat_homogeneous 960)).mul hj').mul (ht'.pow 2)).mul (hh'.pow 2)
  have m7 := ((((nat_homogeneous 1200)).mul hj').mul (ht'.pow 3)).mul hh'
  have m8 := (((nat_homogeneous 480)).mul (hj'.pow 2)).mul (hh'.pow 3)
  have m9 := ((((nat_homogeneous 480)).mul (hj'.pow 2)).mul ht').mul (hh'.pow 2)
  have m10 := ((((nat_homogeneous 840)).mul (hj'.pow 2)).mul (ht'.pow 2)).mul hh'
  have m11 := (((nat_homogeneous 240)).mul (hj'.pow 3)).mul (hh'.pow 2)
  have m12 := ((((nat_homogeneous 240)).mul (hj'.pow 3)).mul ht').mul hh'
  have m13 := (((nat_homogeneous 960)).mul hb').mul (hh'.pow 4)
  have m14 := ((((nat_homogeneous 640)).mul hb').mul ht').mul (hh'.pow 3)
  have m15 := ((((nat_homogeneous 1440)).mul hb').mul (ht'.pow 2)).mul (hh'.pow 2)
  have m16 := ((((nat_homogeneous 1440)).mul hb').mul (ht'.pow 3)).mul hh'
  have m17 := ((((nat_homogeneous 640)).mul hb').mul hj').mul (hh'.pow 3)
  have m18 := (((((nat_homogeneous 960)).mul hb').mul hj').mul ht').mul (hh'.pow 2)
  have m19 := (((((nat_homogeneous 1440)).mul hb').mul hj').mul (ht'.pow 2)).mul hh'
  have m20 := ((((nat_homogeneous 480)).mul hb').mul (hj'.pow 2)).mul (hh'.pow 2)
  have m21 := (((((nat_homogeneous 480)).mul hb').mul (hj'.pow 2)).mul ht').mul hh'
  have partial0 := ((((m0).add m1).sub m2).add m3).add m4
  have partial1 := ((((partial0).sub m5).add m6).sub m7).sub m8
  have partial2 := ((((partial1).sub m9).add m10).add m11).sub m12
  have partial3 := ((((partial2).sub m13).add m14).sub m15).add m16
  have partial4 := ((((partial3).add m17).add m18).sub m19).sub m20
  exact (partial4).add m21

private theorem evaluate_form (caps : Fin 5 → Cap) (w : Fin 5 → ℚ) :
    eval w (form caps) =
      bend (∑ i : Fin 5, ((caps i).1.b : ℚ) * w i) (∑ i : Fin 5, ((caps i).1.j : ℚ) * w i)
        (∑ i : Fin 5, ((caps i).1.t : ℚ) * w i) (∑ i : Fin 5, ((caps i).2 : ℚ) * w i) := by
  simp only [form, bend, linear, map_add, map_sub, map_mul, map_pow, map_neg,
    map_ofNat, map_sum, eval_C, eval_X]

private theorem eval_zero_diagonal (caps : Fin 5 → Cap) (J : Finset (Fin 5)) :
    eval (zeroDiagonal J) (form caps) =
      (Low48Price.bentIntegral (Low48BentLattice.Sum J caps).1.b (Low48BentLattice.Sum J caps).1.j (Low48BentLattice.Sum J caps).1.t (Low48BentLattice.Sum J caps).2 : ℚ) := by
  classical
  rw [evaluate_form]
  simp only [zeroDiagonal, mul_ite, mul_one, mul_zero, Finset.sum_ite_mem, Finset.univ_inter,
    Low48BentLattice.Sum, Nat.cast_sum, Low48Price.bentIntegral, bend]
  push_cast
  rfl

private theorem eval_positive_diagonal (caps : Fin 5 → Cap) (J : Finset (Fin 5)) :
    let p := Low48BentLattice.Sum univ (fun i => Scale (positiveDiagonal J i) (caps i))
    eval (fun i => (positiveDiagonal J i : ℚ)) (form caps) =
      (Low48Price.bentIntegral p.1.b p.1.j p.1.t p.2 : ℚ) := by
  rw [evaluate_form]
  simp only [Low48BentLattice.Sum, Scale, Shape.scale, Nat.cast_sum, Nat.cast_mul, Low48Price.bentIntegral, bend]
  push_cast
  simp only [mul_comm]

theorem remove_baseline (caps : Fin 5 → Cap) :
    (∑ J ∈ (univ : Finset (Fin 5)).powerset, (-1 : ℚ) ^ (5 - J.card) *
      (let p := Low48BentLattice.Sum univ (fun i => Scale (positiveDiagonal J i) (caps i))
       (Low48Price.bentIntegral p.1.b p.1.j p.1.t p.2 : ℚ))) =
      ∑ J ∈ (univ : Finset (Fin 5)).powerset, (-1 : ℚ) ^ (5 - J.card) *
        (Low48Price.bentIntegral (Low48BentLattice.Sum J caps).1.b (Low48BentLattice.Sum J caps).1.j (Low48BentLattice.Sum J caps).1.t (Low48BentLattice.Sum J caps).2 : ℚ) := by
  simp_rw [← eval_positive_diagonal, ← eval_zero_diagonal]
  have hhom := homogeneousComponent_eq_self (form_homogeneous caps)
  have h5 : 5 = (univ : Finset (Fin 5)).card := by simp
  calc
    _ = (form caps).coeff (squarefree univ) := by
      have hs := cube_extract univ (form caps)
      simp_rw [line_coeff, ← h5, hhom] at hs
      exact hs
    _ = _ := by
      rw [← zero_cube (form caps), hhom]

end
end Low48BentPolarization

end Merged_Low48BentPolarization

-- merged module Low48BentCyclePrice
section Merged_Low48BentCyclePrice

set_option autoImplicit false
set_option Elab.async false

namespace Low48BentCycle

noncomputable section

open Low48BentLattice (Cap Chamber latticePoints)
open Low48Price (addBent ambientMix bentIntegral)
open K1_13 (Shape)
open K1_13_6_2_4_1 (positiveDiagonal)
open scoped BigOperators

def integral (a : Cap) : ℤ := bentIntegral a.1.b a.1.j a.1.t a.2

def slots : List (Fin 5) := [0, 1, 2, 3, 4]

private theorem sublists_slots :
    (↑(slots.sublists.map List.toFinset) : Multiset (Finset (Fin 5))) =
      (Finset.univ : Finset (Fin 5)).powerset.val := by
  decide

private theorem fold_cap (B : Fin 5 → Cap) (l : List (Fin 5)) (hl : l.Nodup) (acc : Cap) :
    (l.map B).foldl addBent acc = Low48BentLattice.Add acc (Low48BentLattice.Sum l.toFinset B) := by
  induction l generalizing acc with
  | nil =>
    rcases acc with ⟨⟨b,j,t⟩, h⟩
    simp [Low48BentLattice.Add, Low48BentLattice.Sum, Shape.plus]
  | cons i l ih =>
    obtain ⟨hi, hl⟩ := List.nodup_cons.mp hl
    rw [List.map_cons, List.foldl_cons, ih hl, List.toFinset_cons]
    simp [Low48BentLattice.Add, addBent, Low48BentLattice.Sum, Shape.plus,
      Finset.sum_insert (mt List.mem_toFinset.mp hi), Nat.add_assoc]

private theorem fold_charge {α : Type*} (f : α → ℤ) (l : List α) (a : ℤ) :
    l.foldl (fun s x => s + f x) a = a + (l.map f).sum := by
  induction l generalizing a with
  | nil => simp
  | cons i l ih => simp [ih, add_assoc]


set_option maxHeartbeats 1000000 in
theorem ambient_list (B : Fin 5 → Cap) :
    ambientMix (slots.map B) =
      (∑ J ∈ (Finset.univ : Finset (Fin 5)).powerset, (-1 : ℤ) ^ (5 - J.card) *
        integral (Low48BentLattice.Sum J B)).toNat := by
  classical
  unfold ambientMix
  let charge := fun J : Finset (Fin 5) => (-1 : ℤ) ^ (5 - J.card) * integral (Low48BentLattice.Sum J B)
  congr 1
  rw [List.sublists_map, fold_charge, zero_add, List.map_map]
  calc
    _ = (slots.sublists.map (charge ∘ List.toFinset)).sum := by
      apply congrArg List.sum
      apply List.map_congr_left
      intro l hl
      have hn := (List.mem_sublists.mp hl).nodup (show slots.Nodup by decide)
      simp only [Function.comp_apply, List.length_map, fold_cap B l hn]
      simp [charge, List.toFinset_card_of_nodup hn, integral, Low48BentLattice.Add, Shape.plus]
    _ = ∑ J ∈ (Finset.univ : Finset (Fin 5)).powerset, charge J := by
      rw [← List.map_map]
      change (Multiset.map charge (↑(slots.sublists.map List.toFinset) :
        Multiset (Finset (Fin 5)))).sum = _
      rw [sublists_slots]
      rfl


end

end Low48BentCycle

end Merged_Low48BentCyclePrice
