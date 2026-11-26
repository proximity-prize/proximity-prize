import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.A6966FinalAnchorSpace
import ProximityPrize.SubmissionLower.Fat6966Factors
import ProximityPrize.SubmissionLower.FrontBranch12
import ProximityPrize.SubmissionLower.Gate6966Gate
import ProximityPrize.SubmissionLower.Low48BentCycleCap
import ProximityPrize.SubmissionLower.Low48BentSupport
import ProximityPrize.SubmissionLower.Low6966Order
import ProximityPrize.SubmissionLower.R6960Front6960Rank4

section Merged6967_Low48BentCyclePrice
set_option Elab.async false



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
open Low48Price (addBent ambientMix bentIntegral primaryBox )
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

end Merged6967_Low48BentCyclePrice

section Merged6967_Low49ActiveLattice
set_option Elab.async false


set_option Elab.async false

set_option autoImplicit false
set_option maxHeartbeats 1400000

namespace Low49ActiveLattice
open Low48BentLattice
open K1_13 (Shape)
open K1_13_6_2_4 (Exponent)
open scoped Pointwise

def Fits (a : Cap) (c : ℕ) : Prop :=
  a.1.j + c ≤ a.1.b ∧ 3*a.1.t ≤ a.1.j ∧ 2*c ≤ a.1.j ∧ c + 2*a.2 ≤ 2*a.1.t ∧ 2*a.2 ≤ c ∧ c%2=0

def Active (m : Exponent) : ℕ := m 1 + m 2 + m 3

def points (a : Cap) (c : ℕ) : Set Exponent :=
  {m | m ∈ latticePoints a ∧ m 0 + 2*Active m + 3*m 4 + 2*c ≤ 2*a.1.b + 2*a.1.j}

theorem fits_add {a b : Cap} {c c' : ℕ} (ha : Fits a c) (hb : Fits b c') :
    Fits (Low48BentLattice.Add a b) (c+c') := by
  obtain ⟨ha₁,ha₂,ha₃,ha₄,ha₅,ha₆⟩ := ha
  obtain ⟨hb₁,hb₂,hb₃,hb₄,hb₅,hb₆⟩ := hb
  simp only [Fits, Low48BentLattice.Add, Shape.plus]
  omega

theorem finite (a : Cap) (c : ℕ) : (points a c).Finite :=
  (Low48BentLattice.finite a).subset fun _ hm => hm.1

instance (a : Cap) (c : ℕ) : Finite (points a c) := (finite a c).to_subtype

private theorem clipBound {u a h c b j p : ℕ}
    (hp : p = a - ((2*j-4*h)-(2*c-2*h)))
    (_hj : 4*h ≤ 2*j) (hc : 2*h ≤ 2*c) (hd : 2*c+2*h ≤ 2*j)
    (hu : u + a + h + p ≤ 2*b) :
    u + a + h ≤ 2*b ∧ u+2*a+3*h+2*c ≤ 2*b+2*j := by omega

private theorem join_threshold {ja jb ca cb h h' t : ℕ}
    (ha : 4*h≤2*ja ∧ 2*h≤2*ca) (hb : 4*h'≤2*jb ∧ 2*h'≤2*cb)
    (ht : h+h'=t) :
    (2*ja-4*h)+(2*jb-4*h')-((2*ca-2*h)+(2*cb-2*h')) =
      2*(ja+jb)-2*(ca+cb)-2*t := by omega

private theorem zero_fit {B J a h c u : ℕ}
    (hb : u+a+h≤B) (hc : u+2*a+3*h+c≤B+J) :
    u+a+h+(a-(J-c-2*h))≤B := by omega

private theorem split_zero {u a b ca cb : ℕ} (ha : a≤ca) (hb : b≤cb)
    (h : u+a+b≤ca+cb) :
    let v := min u (ca-a)
    v+(u-v)=u ∧ v+a≤ca ∧ u-v+b≤cb := by
  dsimp
  omega

theorem add {a b : Cap} {c c' : ℕ} (ha : Fits a c) (hb : Fits b c') :
    points a c + points b c' = points (Low48BentLattice.Add a b) (c+c') := by
  ext m
  constructor
  · rintro ⟨x,hx,y,hy,rfl⟩
    simp only [points, Set.mem_ofPred_eq, coords, Active, Low48BentLattice.Add,
      Shape.plus, Finsupp.add_apply] at *
    omega
  · intro hm
    obtain ⟨haB,haJ,hacJ,hacT,hacH,haP⟩ := ha
    obtain ⟨hbB,hbJ,hbcJ,hbcT,hbcH,hbP⟩ := hb
    simp only [points, Set.mem_ofPred_eq, coords, Active, Low48BentLattice.Add, Shape.plus] at hm
    obtain ⟨⟨hmB,hmJ,hmT,hmH⟩,hmC⟩ := hm
    let h := min (m 4) (2*a.2)
    let h' := m 4-h
    have hh : h+h'=m 4 ∧ h≤2*a.2 ∧ h'≤2*b.2 := by dsimp [h,h']; omega
    have hA : 4*h≤2*a.1.j ∧ 2*h≤2*c ∧ 2*c+2*h≤2*a.1.j := by
      clear * - hh haJ hacJ hacT hacH
      omega
    have hB : 4*h'≤2*b.1.j ∧ 2*h'≤2*c' ∧ 2*c'+2*h'≤2*b.1.j := by
      clear * - hh hbJ hbcJ hbcT hbcH
      omega
    let ja := 2*a.1.j-4*h
    let jb := 2*b.1.j-4*h'
    let ta := 2*a.1.t-2*h
    let tb := 2*b.1.t-2*h'
    let ca := 2*c-2*h
    let cb := 2*c'-2*h'
    have haW : 3*ta≤ja ∧ 2*ca≤ja ∧ ca≤2*ta := by dsimp [ja,ta,ca]; omega
    have hbW : 3*tb≤jb ∧ 2*cb≤jb ∧ cb≤2*tb := by dsimp [jb,tb,cb]; omega
    have he : ja%2=0 ∧ jb%2=0 ∧ ta%2=0 ∧ tb%2=0 ∧ ca%2=0 ∧ cb%2=0 := by
      dsimp [ja,jb,ta,tb,ca,cb]
      omega
    have hodd : h%2=0 ∨ h'%2=0 := by dsimp [h,h']; omega
    have hParity : (ca/2)%2=0 ∨ (cb/2)%2=0 := by dsimp [ca,cb]; omega
    have hIn : m 3 ≤ ta+tb ∧ m 1+2*m 2+3*m 3 ≤ ja+jb := by
      dsimp [ta,tb,ja,jb]
      omega
    obtain ⟨x,x',y,y',t,t',hx,hy,ht,hta,htb,hja,hjb,hp⟩ :=
      Low49ActiveSplit.split (x:=m 1) (y:=m 2) (z:=m 3) haW hbW he hParity hIn
    let w := x+y+t
    let w' := x'+y'+t'
    let pa := w-(ja-ca)
    let pb := w'-(jb-cb)
    have hwa : w≤ja ∧ pa≤ca := by clear * - hja; dsimp [w,pa]; omega
    have hwb : w'≤jb ∧ pb≤cb := by clear * - hjb; dsimp [w',pb]; omega
    have hbs : w+h+pa ≤ 2*a.1.b := by
      clear * - hA hwa haB
      dsimp [ja,ca] at hwa
      omega
    have hbs' : w'+h'+pb ≤ 2*b.1.b := by
      clear * - hB hwb hbB
      dsimp [jb,cb] at hwb
      omega
    have hW : w+w' = m 1+m 2+m 3 := by
      unfold w w'
      rw [← hx,← hy,← ht]
      ac_rfl
    have hJ : ja+jb-(ca+cb) = 2*(a.1.j+b.1.j)-2*(c+c')-2*m 4 :=
      join_threshold ⟨hA.1,hA.2.1⟩ ⟨hB.1,hB.2.1⟩ hh.1
    have hp' : pa+pb = m 1+m 2+m 3 -
        (2*(a.1.j+b.1.j)-2*(c+c')-2*m 4) := by
      rw [← hJ]
      exact hp
    have hzero : m 0 + (w+h+pa) + (w'+h'+pb) ≤ 2*a.1.b+2*b.1.b := by
      have hs := zero_fit (B:=2*(a.1.b+b.1.b)) (J:=2*(a.1.j+b.1.j))
        (a:=m 1+m 2+m 3) (h:=m 4) (c:=2*(c+c')) (u:=m 0) (by clear * - hmB; omega) (by clear * - hmC; omega)
      rw [← hp',← hW,← hh.1, Nat.mul_add] at hs
      simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hs
    let u := min (m 0) (2*a.1.b-(w+h+pa))
    let u' := m 0-u
    have hu : u+u'=m 0 ∧ u+w+h+pa≤2*a.1.b ∧ u'+w'+h'+pb≤2*b.1.b := by
      simpa only [u,u',Nat.add_assoc] using split_zero hbs hbs' hzero
    have hb₁ := clipBound (u:=u) (a:=w) (h:=h) (c:=c) (b:=a.1.b) (j:=a.1.j)
      (p:=pa) rfl hA.1 hA.2.1 hA.2.2 hu.2.1
    have hb₂ := clipBound (u:=u') (a:=w') (h:=h') (c:=c') (b:=b.1.b) (j:=b.1.j)
      (p:=pb) rfl hB.1 hB.2.1 hB.2.2 hu.2.2
    let v : Exponent := Finsupp.equivFunOnFinite.symm ![u,x,y,t,h]
    let v' : Exponent := Finsupp.equivFunOnFinite.symm ![u',x',y',t',h']
    refine ⟨v, ?_, v', ?_, ?_⟩
    · simp only [points, Set.mem_ofPred_eq, coords, Active]
      change (u+x+y+t+h≤2*a.1.b ∧ x+2*y+3*t+4*h≤2*a.1.j ∧ t+2*h≤2*a.1.t ∧ h≤2*a.2) ∧
        u+2*(x+y+t)+3*h+2*c≤2*a.1.b+2*a.1.j
      refine ⟨⟨?_,?_,?_,hh.2.1⟩,hb₁.2⟩
      · simpa only [w,Nat.add_assoc] using hb₁.1
      · clear * - hja hA
        dsimp [ja] at hja
        omega
      · clear * - hta hh hacH hacT
        dsimp [ta] at hta
        omega
    · simp only [points, Set.mem_ofPred_eq, coords, Active]
      change (u'+x'+y'+t'+h'≤2*b.1.b ∧ x'+2*y'+3*t'+4*h'≤2*b.1.j ∧ t'+2*h'≤2*b.1.t ∧ h'≤2*b.2) ∧
        u'+2*(x'+y'+t')+3*h'+2*c'≤2*b.1.b+2*b.1.j
      refine ⟨⟨?_,?_,?_,hh.2.2⟩,hb₂.2⟩
      · simpa only [w',Nat.add_assoc] using hb₂.1
      · clear * - hjb hB
        dsimp [jb] at hjb
        omega
      · clear * - htb hh hbcH hbcT
        dsimp [tb] at htb
        omega
    · ext i
      fin_cases i
      · exact hu.1
      · exact hx
      · exact hy
      · exact ht
      · exact hh.1

end Low49ActiveLattice

end Merged6967_Low49ActiveLattice

section Merged6967_Low6966AllocCore
set_option Elab.async false




set_option Elab.async false

namespace Low6966MassCheck
open Final50Price (layerNeed)
open K1_13 (Shape remaining)
open K1_13_8 (zeroShape)
open Final50PriceLayer (fastLayer availableMass)
open K1_13_8_2 (Threshold)
open P0_9_8 (symbol_count)
open P3_6_8_1 (sumBelow sumBelow_eq sumBelow_add)
theorem mass_eq (r y : Shape) (L : ℕ) (hr : r = zeroShape ∨ 0 < r.j)
    (hj : 0 < r.j+y.j) : availableMass r y L =
    P3_6_8_1.sumBelow (fastLayer r y L) (L + 1650 / (r.j+y.j)) := by
  rw [P3_6_8_1.sumBelow_eq, Final50PriceLayer.availableMass_eq_sum hr hj le_rfl]
def check (f : ℕ → ℕ) (offset length : ℕ) : List ℕ → Bool
  | [] => decide (length = 0)
  | v :: vs =>
      decide (P3_6_8_1.sumBelow (fun k => f (offset + k)) (min length 12) = v) &&
        check f (offset + min length 12) (length - 12) vs
theorem check_sum (f : ℕ → ℕ) (offset length : ℕ) (values : List ℕ)
    (h : check f offset length values = true) :
    P3_6_8_1.sumBelow f (offset + length) = P3_6_8_1.sumBelow f offset + values.sum := by
  induction values generalizing offset length with
  | nil =>
    have hz : length = 0 := of_decide_eq_true h
    simp [hz]
  | cons v vs ih =>
    have hv : P3_6_8_1.sumBelow (fun k => f (offset + k)) (min length 12) = v :=
      of_decide_eq_true (Bool.and_eq_true_iff.mp h).1
    have hr := (Bool.and_eq_true_iff.mp h).2
    have hs : min length 12 + (length - 12) = length := by omega
    calc
      _ = P3_6_8_1.sumBelow f (offset + min length 12 + (length - 12)) := by rw [Nat.add_assoc, hs]
      _ = P3_6_8_1.sumBelow f (offset + min length 12) + vs.sum := ih _ _ hr
      _ = _ := by rw [P3_6_8_1.sumBelow_add, hv, List.sum_cons, Nat.add_assoc]
end Low6966MassCheck

-- merged module R6960Low6966AllocCore
section Merged_R6960Low6966AllocCore

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 3000000
set_option maxRecDepth 16000

namespace Low6966Allocation
open Finset
open K1_13 (Shape InBox)
open K1_13_8 (zeroShape Valid)
open K1_13_8_2 (Threshold orderFor)
open Final50PriceLayer (availableMass fastLayer layerTerm)
open LowProfile6966 (lowDegreeCap)
open Low6966Retained (Box)
open LowProfile6966 (retainedTariff need layerCount)
open LowProfile6966 (degree_bound)
open Low6966MassCheck (check check_sum mass_eq)
open P3_6_8_1 (sumBelow)
open scoped BigOperators Classical

abbrev Band := Fin 34
abbrev empty : Band := 0

structure BandData where
  lo : ℕ
  hi : ℕ
  index : ℕ
  top : ℕ
  charge : ℕ

private def bands : List BandData := [
  ⟨0,0,0,0,0⟩,
  ⟨1,1,3,1,2158343791299739⟩,
  ⟨2,2,3,1,2158343791299739⟩,
  ⟨3,3,3,1,2158343791299739⟩,
  ⟨4,4,3,1,2502144872790737⟩,
  ⟨5,5,3,1,2853169289624949⟩,
  ⟨6,6,3,1,3213531186026336⟩,
  ⟨7,7,3,1,3585344706218855⟩,
  ⟨8,8,3,1,3970723994426466⟩,
  ⟨9,9,3,1,4371783194873127⟩,
  ⟨2,2,4,1,5084581920206611⟩,
  ⟨3,3,4,1,5084581920206611⟩,
  ⟨5,13,4,1,13288828112236049⟩,
  ⟨10,20,3,1,10422953855615941⟩,
  ⟨21,27,3,1,16682238211103677⟩,
  ⟨4,4,4,1,5084581920206611⟩,
  ⟨14,25,4,1,27801785010375170⟩,
  ⟨2,16,5,1,29321008282042400⟩,
  ⟨17,22,5,1,40884529399089500⟩,
  ⟨2,19,6,1,50034357782895031⟩,
  ⟨2,7,6,2,69920260416388496⟩,
  ⟨8,10,6,2,96169042992307818⟩,
  ⟨11,12,6,2,114050562090214412⟩,
  ⟨13,16,6,2,151035649024996992⟩,
  ⟨17,19,6,2,180110155019963563⟩,
  ⟨3,14,7,1,50237673053923854⟩,
  ⟨3,5,7,2,110707568104725464⟩,
  ⟨6,8,7,2,123787931603989937⟩,
  ⟨9,11,7,2,163437076454291587⟩,
  ⟨12,13,7,2,190294455821989800⟩,
  ⟨14,14,7,2,203875901598210081⟩,
  ⟨3,6,8,1,41777586260844276⟩,
  ⟨3,3,8,2,176274052417450246⟩,
  ⟨4,6,8,2,176274052417450299⟩]

def band (k : Band) : BandData := bands.get ⟨k.val,k.isLt⟩

def start (k : Band) : Shape := ⟨(band k).lo,(band k).index,(band k).top⟩

def endWidth (k : Band) : ℕ := (band k).hi

def reserve (k : Band) : ℕ := (band k).charge

def Admits (k : Band) (r : Shape) : Prop :=
  (start k).b≤r.b ∧ r.b≤endWidth k ∧ r.j=(start k).j ∧ r.t=(start k).t

instance (k : Band) (r : Shape) : Decidable (Admits k r) := by unfold Admits; infer_instance

theorem start_flat (k : Band) : start k=zeroShape ∨ 0<(start k).j := by
  fin_cases k <;> decide +kernel

theorem empty_admits : Admits empty zeroShape := by decide +kernel

theorem admits_floor {k : Band} {r : Shape} (hr : Admits k r) : InBox (start k) r :=
  ⟨hr.1,hr.2.2.1.symm.le,hr.2.2.2.symm.le⟩

private theorem checked_cover (b : Fin 28) :
    ∀ (j : Fin 9) (t : Fin 3), 1≤t.val → 3*t.val≤j.val → j.val≤3*b.val →
      b.val≤lowDegreeCap j.val → ∃ k : Band, Admits k ⟨b.val,j.val,t.val⟩ := by
  fin_cases b <;> decide +kernel

theorem choose_band (r : Shape) (v : Valid r) (box : Box r) : ∃ k : Band,Admits k r := by
  rcases r with ⟨b,j,t⟩
  have hb : b<28 := Nat.lt_succ_of_le box.1
  have hj : j<9 := Nat.lt_succ_of_le box.2.1
  have ht : t<3 := by have := v.2.1; change 3*t≤j at this; omega
  exact checked_cover ⟨b,hb⟩ ⟨j,hj⟩ ⟨t,ht⟩ v.1 v.2.1 v.2.2 (degree_bound v box)

private theorem checked_reserve (k : Band) :
    ∀ b : Fin 28,(start k).b≤b.val → b.val≤endWidth k →
      retainedTariff b.val (start k).j (start k).t≤reserve k := by
  fin_cases k <;> decide +kernel

theorem admits_fee {k : Band} {r : Shape} (hr : Admits k r) :
    retainedTariff r.b r.j r.t≤reserve k := by
  have hm : endWidth k<28 := by fin_cases k <;> decide +kernel
  rw [hr.2.2.1,hr.2.2.2]
  exact checked_reserve k ⟨r.b,hr.2.1.trans_lt hm⟩ hr.1 hr.2.1

abbrev budget : ℕ := 274785163470701553

def factorCap (top : ℕ) : ℕ := budget-Low6966Prices.lowerCap top

def tiered (k : Band) : Bool := k.val == 1 || k.val == 32

def pricingWeight (k : Band) (b j t : ℕ) : ℕ :=
  if k=empty then Low6966AllocWeight.weight b j t else if tiered k then Research6966.LowTierWeight.weight (58-(start k).j) j else j

def pricingDenom (k : Band) : ℕ := if k=empty then 374 else if tiered k then 5*(58-(start k).j) else 58-(start k).j

def allowance (k : Band) (top b j t : ℕ) : ℕ :=
  (factorCap top-reserve k)*pricingWeight k b j t/pricingDenom k

theorem denom_pos (k : Band) : 0<pricingDenom k := by fin_cases k <;> decide +kernel

theorem reserve_fits (top : ℕ) (ht : top≤15) (k : Band) : reserve k≤factorCap top := by
  interval_cases top <;> fin_cases k <;> decide +kernel

theorem weight_mono (k : Band) {b j t B J T : ℕ} (hb : b≤B) (hj : j≤J) (ht : t≤T) :
    pricingWeight k b j t≤pricingWeight k B J T := by
  by_cases h : k=empty
  · simpa only [pricingWeight,ite_eq_left h] using Low6966AllocWeight.mono hb hj ht
  · by_cases t : tiered k
    · simpa [pricingWeight,h,t] using Research6966.LowTierWeight.mono (58-(start k).j) hj
    · simpa [pricingWeight,h,t] using hj

theorem allowance_mono {a b w j t : ℕ} (k : Band) (h : a≤b) (hb : b≤15) :
    allowance k a w j t≤allowance k b w j t := by
  have pos : factorCap a≤factorCap b := by
    have ha := h.trans hb
    interval_cases a <;> interval_cases b <;> decide +kernel
  exact Nat.div_le_div_right (Nat.mul_le_mul_right _ (Nat.sub_le_sub_right pos _))

def MassCell (k : Band) :=
  {q : Threshold // 0<q.j ∧ availableMass (start k) ⟨q.b,q.j,0⟩ (q.l-1)<need}

theorem mass_cell (k : Band) (b j l N : ℕ) (hj : 0<j)
    (hN : (l-1)+1650/((start k).j+j)=N) (vals : List ℕ)
    (worked : check (fastLayer (start k) ⟨b,j,0⟩ (l-1)) 0 N vals=true)
    (small : vals.sum<need) :
    0<(⟨b,j,l⟩ : Threshold).j ∧
      availableMass (start k) ⟨b,j,0⟩ (l-1)<need := by
  refine ⟨hj,?_⟩
  rw [mass_eq _ _ _ (start_flat k) (by change 0<(start k).j+j; omega),hN]
  have sum := check_sum (fastLayer (start k) ⟨b,j,0⟩ (l-1)) 0 N vals worked
  have eq : P3_6_8_1.sumBelow (fastLayer (start k) ⟨b,j,0⟩ (l-1)) N=vals.sum := by
    simpa only [Nat.zero_add,P3_6_8_1.sumBelow] using sum
  rwa [eq]

def order {k : Band} (cells : List (MassCell k)) (x : Shape) : ℕ :=
  orderFor x.b x.j (cells.map Subtype.val)

theorem order_pos {k : Band} (cells : List (MassCell k)) (x : Shape) : 0<order cells x :=
  (P0_9_8.orderFor_select x.b x.j (cells.map Subtype.val)).1

theorem order_mono {k : Band} (cells : List (MassCell k)) {x y : Shape}
    (hb : x.b≤y.b) (hj : x.j≤y.j) : order cells x≤order cells y :=
  P0_9_8.orderFor_mono hb hj _

theorem order_valid {k : Band} (cells : List (MassCell k)) (x : Shape) : order cells x=1 ∨
    availableMass (start k) x (order cells x-1)<need := by
  rcases (P0_9_8.orderFor_select x.b x.j (cells.map Subtype.val)).2 with h | ⟨q,hq,hb,hj,eq⟩
  · exact Or.inl h
  · obtain ⟨c,_,rfl⟩ := List.mem_map.mp hq
    refine Or.inr ?_
    change order cells x=c.val.l at eq
    rw [eq]
    have pos : 0<(start k).j+c.val.j := by have := c.property.1; omega
    exact (Final50PriceLayer.availableMass_anti_prefix (y:=⟨c.val.b,c.val.j,0⟩)
      (start_flat k) pos hb hj).trans_lt c.property.2

theorem layer_le_available {r y : Shape} {L : ℕ}
    (hr : r=zeroShape ∨ 0<r.j) (hj : 0<r.j+y.j) :
    (∑ k∈range layerCount,layerTerm r y L k)≤availableMass r y L := by
  exact Final50PriceLayer.layerSum_le_available_n _ hr hj

#print axioms choose_band
#print axioms order_valid

end Low6966Allocation

end
end Merged_R6960Low6966AllocCore


end Merged6967_Low6966AllocCore

section Merged6967_Low6966FatPad
set_option Elab.async false



set_option Elab.async false
section
namespace Low6966FatPad
noncomputable section
open Polynomial Finset
open P3 (K I node)
open Low6966Prices (Messages taylorLength)
def membershipTest (g : K1_13.Row 4) : K1_13.Row 4 :=
  K1_13_6.jetNumerator g taylorLength
open K1_14_6 (occupancy)
open P0_10 (incidence_arithmetic)
open K1_13_6 (CurveSections SurfaceSections Pieces)
open ProximityPrize.Benchmark
open scoped BigOperators
theorem section_capacity {w Γ s} (h : Messages w Γ s) (d : ℕ)
    (hsection : ∀ i : I, (∃ γ ∈ Γ, (s γ).eval (node i) ≠ w i) →
      (Γ.filter fun γ => (s γ).eval (node i) = w i).card ≤ d) :
    46372 * Γ.card ≤ 82385*d + 46372 := by
  classical
  by_cases hm : Γ.card ≤ 1
  · omega
  let hits (γ : K) : Finset I := univ.filter fun i => (s γ).eval (node i) = w i
  let common : Finset I := univ.filter fun i => ∀ γ ∈ Γ, (s γ).eval (node i) = w i
  let nodes : Finset I := univ \ common
  have common_le (γ : K) (hγ : γ ∈ Γ) : common ⊆ hits γ := by
    intro i hi
    exact mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hi).2 γ hγ⟩
  have hit_count (γ : K) (hγ : γ ∈ Γ) : 179759 ≤ (hits γ).card := by
    obtain ⟨T, hT, ht⟩ := h.hits γ hγ
    exact hT.trans (card_le_card fun i hi => mem_filter.mpr ⟨mem_univ _, ht i hi⟩)
  have pair_count (a : K) (ha : a ∈ Γ) (b : K) (hb : b ∈ Γ) (hab : a ≠ b) :
      (hits a ∩ hits b).card ≤ 133387 := by
    let P := s a - s b
    have hp : P ≠ 0 := sub_ne_zero.mpr fun eq => hab (h.distinct ha hb eq)
    refine (FrobeniusLocator.Strata.root_nodes_card_le node IRSProfile.domain.injective
      P hp _ ?_).trans ((natDegree_sub_le _ _).trans (max_le (h.degree a ha) (h.degree b hb)))
    intro i hi
    rw [eval_sub, (mem_filter.mp (mem_inter.mp hi).1).2, (mem_filter.mp (mem_inter.mp hi).2).2,
      sub_self]
  obtain ⟨a, ha, b, hb, hab⟩ := one_lt_card.mp (by omega : 1 < Γ.card)
  have hcommon : common.card ≤ 133387 :=
    (card_le_card (subset_inter (common_le a ha) (common_le b hb))).trans
      (pair_count a ha b hb hab)
  let x := 179759 - common.card
  let t := 133387 - common.card
  have ht : t = x - 46372 := by dsimp [t, x]; omega
  have hx : 46372 ≤ x := by dsimp [x]; omega
  have hnodes : nodes.card = x + 82385 := by
    rw [card_sdiff_of_subset (subset_univ common), card_univ, IRSProfile.card_index]
    dsimp [x]
    omega
  have exists_trim (γ : K) :
      ∃ T : Finset I, γ ∈ Γ → T ⊆ hits γ \ common ∧ T.card = x := by
    by_cases hγ : γ ∈ Γ
    · have hc := hit_count γ hγ
      have hd : x ≤ (hits γ \ common).card := by
        rw [card_sdiff_of_subset (common_le γ hγ)]
        dsimp [x]
        omega
      obtain ⟨T, hT, hcT⟩ := exists_subset_card_eq hd
      exact ⟨T, fun _ => ⟨hT, hcT⟩⟩
    · exact ⟨∅, fun h => (hγ h).elim⟩
  choose T hT using exists_trim
  have into_nodes (γ : K) (hγ : γ ∈ Γ) : T γ ⊆ nodes := by
    intro i hi
    exact mem_sdiff.mpr ⟨mem_univ _, (mem_sdiff.mp ((hT γ hγ).1 hi)).2⟩
  have overlap (a : K) (ha : a ∈ Γ) (b : K) (hb : b ∈ Γ) (hab : a ≠ b) :
      (T a ∩ T b).card ≤ t := by
    have cover : (T a ∩ T b) ∪ common ⊆ hits a ∩ hits b := by
      intro i hi
      rcases mem_union.mp hi with ht' | hc
      · exact mem_inter.mpr ⟨(mem_sdiff.mp ((hT a ha).1 (mem_inter.mp ht').1)).1,
          (mem_sdiff.mp ((hT b hb).1 (mem_inter.mp ht').2)).1⟩
      · exact mem_inter.mpr ⟨common_le a ha hc, common_le b hb hc⟩
    have disj : Disjoint (T a ∩ T b) common := disjoint_left.mpr fun i hi hi' =>
      (mem_sdiff.mp (into_nodes a ha (mem_inter.mp hi).1)).2 hi'
    have hc := (card_le_card cover).trans (pair_count a ha b hb hab)
    rw [card_union_of_disjoint disj] at hc
    dsimp [t]
    omega
  have occ_le (i : I) (hi : i ∈ nodes) :
      (Γ.filter fun γ => i ∈ T γ).card ≤ d := by
    have proper : ∃ γ ∈ Γ, (s γ).eval (node i) ≠ w i := by
      by_contra! hc
      exact (mem_sdiff.mp hi).2 (mem_filter.mpr ⟨mem_univ _, hc⟩)
    refine (card_le_card ?_).trans (hsection i proper)
    intro γ hγ
    obtain ⟨hγ, hi⟩ := mem_filter.mp hγ
    exact mem_filter.mpr ⟨hγ, (mem_filter.mp (mem_sdiff.mp ((hT γ hγ).1 hi)).1).2⟩
  obtain ⟨sec, first⟩ := occupancy Γ nodes T x t d
    (fun γ hγ => ⟨into_nodes γ hγ, (hT γ hγ).2⟩) overlap occ_le
  rw [hnodes, ht] at sec
  rw [hnodes] at first
  exact incidence_arithmetic 82385 _ _ 46372 _ (by omega) (by decide) hx (by decide) sec first
theorem curve_capacity {w Γ s d} (h : Messages w Γ s) (hc : CurveSections Γ s d) :
    46372 * Γ.card ≤ 82385*d + 46372 :=
  section_capacity h d (fun i => hc (node i) (w i))
theorem curve_capacity_integral {w Γ s d} (h : Messages w Γ s)
    (hc : CurveSections Γ s d) (hd : 0 < d) : Γ.card ≤ 2*d := by
  have := curve_capacity h hc
  omega
theorem pieces_curve_capacity {w Γ s} (C : Pieces Γ) (h : Messages w Γ s)
    (hc : C.curves s) : 46372 * C.union.card ≤ 82385 * C.total + 46372 * C.n := by
  classical
  have hc' (i : Fin C.n) := Low6966FatPad.curve_capacity (Low6966Prices.Messages.mono h (C.subset i)) (hc i)
  calc
    _ ≤ 46372 * ∑ i, (C.piece i).card :=
      Nat.mul_le_mul_left _ (by exact card_biUnion_le)
    _ = ∑ i, 46372 * (C.piece i).card := by rw [mul_sum]
    _ ≤ ∑ i : Fin C.n, (82385 * C.degree i + 46372) := sum_le_sum fun i _ => hc' i
    _ = _ := by simp [Pieces.total, sum_add_distrib, mul_sum, Nat.mul_comm]
theorem pieces_curve_capacity_integral {w Γ s} (C : Pieces Γ) (h : Messages w Γ s)
    (hc : C.curves s) (hd : ∀ i, 0 < C.degree i) : C.union.card ≤ 2*C.total := by
  classical
  have hc' (i : Fin C.n) := Low6966FatPad.curve_capacity_integral (Low6966Prices.Messages.mono h (C.subset i)) (hc i) (hd i)
  calc
    _ ≤ ∑ i, (C.piece i).card := card_biUnion_le
    _ ≤ ∑ i : Fin C.n, 2 * C.degree i := sum_le_sum fun i _ => hc' i
    _ = _ := by simp [Pieces.total, mul_sum]
theorem surface_capacity {w Γ s d} (h : Messages w Γ s)
    (hs : SurfaceSections Γ s d) (hd : 0 < d) : Γ.card ≤ 4*d := by
  classical
  have hsection (i : I) (hi : ∃ γ ∈ Γ, (s γ).eval (node i) ≠ w i) :
      (Γ.filter fun γ => (s γ).eval (node i) = w i).card ≤ 2*d := by
    obtain ⟨C, hC, hc, hpos, hdeg⟩ := hs (node i) (w i) hi
    have hH := Low6966Prices.Messages.mono h (filter_subset (fun γ => (s γ).eval (node i) = w i) Γ)
    exact (card_le_card hC).trans ((pieces_curve_capacity_integral C hH hc hpos).trans
      (Nat.mul_le_mul_left 2 hdeg))
  have := section_capacity h (2*d) hsection
  omega
theorem pieces_surface_capacity {w Γ s} (C : Pieces Γ) (h : Messages w Γ s)
    (hc : C.surfaces s) (hd : ∀ i, 0 < C.degree i) : C.union.card ≤ 4*C.total := by
  classical
  have hc' (i : Fin C.n) := Low6966FatPad.surface_capacity (Low6966Prices.Messages.mono h (C.subset i)) (hc i) (hd i)
  calc
    _ ≤ ∑ i, (C.piece i).card := card_biUnion_le
    _ ≤ ∑ i : Fin C.n, 4 * C.degree i := sum_le_sum fun i _ => hc' i
    _ = _ := by simp [Pieces.total, mul_sum]
end
end Low6966FatPad
end
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 1600
namespace Low6966FatPad
noncomputable section
open K1_13 K1_13_6 K1_13_6_3 K1_13_6_3_5 K1_13_6_3_5_3 MvPolynomial
open scoped Polynomial WithZero
attribute [local instance] MvPolynomial.gradedAlgebra
open K1_13_6_3_5_3 (tupleHeight_le_of_inclusion finsum_weighted cone_eval_jets jet_zero_nonzero)
def ShortSupport (A : CoeffIdeal) : Prop :=
  ∀ i : Fin K1_13.taylorLength, Low6966Prices.taylorLength ≤ i.val → MvPolynomial.X i ∈ A

private theorem principal_divisors : K1_13_6_3_5_3.c2 :=
  K1_13_6_3_5_3_2.of_children K1_13_6_3_5_3_2_1.proof K1_13_6_3_5_3_2_2.proof
private theorem projective_height : K1_13_6_3_5_3.c3 :=
  K1_13_6_3_5_3_3.of_children K1_13_6_3_5_3_3_1.proof K1_13_6_3_5_3_3_2.proof
    K1_13_6_3_5_3_3_3.proof K1_13_6_3_5_3_3_4.proof
private theorem degree_of_support {R : CoeffIdeal} (D : FreshCurve R) (hs : ShortSupport R) :
    D.polynomial.natDegree ≤ 133387 := by
  by_contra h
  let i : Fin taylorLength := ⟨D.polynomial.natDegree, Nat.lt_succ_iff.mpr D.degree_le⟩
  have hi : Low6966Prices.taylorLength ≤ i.val := Nat.lt_of_not_ge h
  have hx : (MvPolynomial.X i : FreshCoeffRing) ∈ extendIdeal R := by
    change (MvPolynomial.X i : FreshCoeffRing) ∈ R.map (MvPolynomial.map geomConstants)
    simpa only [MvPolynomial.map_X] using
      Ideal.mem_map_of_mem (MvPolynomial.map geomConstants) (hs i hi)
  rw [D.equation, coneIdeal, RingHom.mem_ker, coneEval, MvPolynomial.eval₂Hom_X'] at hx
  change Polynomial.C (D.coefficients i) * Polynomial.X = 0 at hx
  have hleading : D.coefficients i = 1 := by
    change D.includeOld (D.polynomial.coeff D.polynomial.natDegree) = 1
    rw [Polynomial.coeff_natDegree, D.monic.leadingCoeff, map_one]
  rw [hleading, Polynomial.C_1, one_mul] at hx
  exact Polynomial.X_ne_zero hx
private theorem multiplicity_bound {m n : ℕ} (hm : m ≤ n) (hn : 2 ≤ n) :
    2 * m ≤ n * min m 2 := by
  by_cases h : m ≤ 2
  · rw [min_eq_left h]
    exact Nat.mul_le_mul_right _ hn
  · rw [min_eq_right (by omega), Nat.mul_comm n 2]
    exact Nat.mul_le_mul_left _ hm
private theorem height_comparison {R : CoeffIdeal} (D : FreshCurve R)
    (hshort : D.polynomial.natDegree ≤ 133387) (hdiv : PrincipalDivisors GeoField D.Fresh) :
    2 * tupleHeight GeoField D.Fresh D.coefficients ≤
      133387 * tupleHeight GeoField D.Fresh (ratios (D.jets (n := 4)) 0) := by
  let : CharP D.Old K1.p := charP_of_injective_ringHom
    ((algebraMap Geom D.Old).comp K1_13.embed).injective K1.p
  have hdeg : D.polynomial.natDegree < taylorLength := Nat.lt_succ_iff.mpr D.degree_le
  have hchar : D.polynomial.natDegree < K1.p := by
    exact D.degree_le.trans_lt (by decide)
  let B := factorsOfMonic D.monic hchar (by decide : 2 < K1.p)
  let z := fun i => (B.factor i).eval₂ D.includeOld D.center
  let r₃ := ratios (D.jets (n := 3)) 0
  let r₄ := ratios (D.jets (n := 4)) 0
  have hc₀ : genericArgument ≠ 0 := by
    have hinj : Function.Injective genericCoeffs :=
      (algebraMap GenericField GeoField).injective.comp
        (IsFractionRing.injective (Polynomial Geom) GenericField)
    simpa only [genericArgument, map_zero] using
      hinj.ne (show (Polynomial.X : (Polynomial Geom)) ≠ 0 from Polynomial.X_ne_zero)
  have hv (v : CurvePlace GeoField D.Fresh) :=
    K1_13_6_3_5_3_6.proof D.Old D.Fresh D.includeOld D.center D.polynomial B v.value
      taylorLength hdeg (v.on_constants _ hc₀) D.independent (K1_13_6_3_5_3_5.proof R D v)
  have hcoeff : tupleHeight GeoField D.Fresh D.coefficients =
      ∑ i, B.multiplicity i * ∑ᶠ v : CurvePlace GeoField D.Fresh, poleOrder v.value (z i) := by
    have hp (v : CurvePlace GeoField D.Fresh) :
        tuplePole v.value D.coefficients = ∑ i, B.multiplicity i * poleOrder v.value (z i) :=
      (hv v).1
    unfold tupleHeight
    simp_rw [hp]
    exact finsum_weighted _ _ (fun i => (hdiv (z i)).1)
  have hjet : tupleHeight GeoField D.Fresh r₃ =
      ∑ i, min (B.multiplicity i) 2 * ∑ᶠ v : CurvePlace GeoField D.Fresh, zeroOrder v.value (z i) := by
    have hp (v : CurvePlace GeoField D.Fresh) :
        tuplePole v.value r₃ = ∑ i, min (B.multiplicity i) 2 * zeroOrder v.value (z i) :=
      (hv v).2
    unfold tupleHeight
    simp_rw [hp]
    exact finsum_weighted _ _ (fun i => (hdiv (z i)).2.1)
  have hmore : tupleHeight GeoField D.Fresh r₃ ≤ tupleHeight GeoField D.Fresh r₄ := by
    apply tupleHeight_le_of_inclusion hdiv r₃ r₄ (Fin.castLE (by decide : 3 ≤ 4))
    intro i
    rfl
  suffices hh : 2 * tupleHeight GeoField D.Fresh D.coefficients ≤
      133387 * tupleHeight GeoField D.Fresh r₃ from
    hh.trans (Nat.mul_le_mul_left _ hmore)
  rw [hcoeff, hjet, Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  rw [(hdiv (z i)).2.2.1, ← mul_assoc, ← mul_assoc]
  apply Nat.mul_le_mul_right
  exact multiplicity_bound ((B.le_degree i).trans hshort) (by decide)
theorem boundary_degree (R : CoeffIdeal) (hR : R.IsPrime) (hprime : (extendIdeal R).IsPrime)
    (hhom : R.IsHomogeneous (homogeneousSubmodule (Fin taylorLength) Geom))
    (hdim : dimension R = 2) (hs : ShortSupport R) :
    dimension (freshImage R) = 2 ∧
      2 * affineDegree (extendIdeal R) ≤
        133387 * (residueDegree freshJetMap (extendIdeal R) : ℚ) * affineDegree (freshImage R) := by
  obtain ⟨D⟩ := K1_13_6_3_5_3_1.proof R hR hprime hhom hdim
  have hdiv := principal_divisors GeoField D.Fresh D.freshCurve
  have hshort := degree_of_support D hs
  let u := D.coefficients
  let v := D.jets (n := 4)
  have hcone : extendIdeal R = coneIdeal GeoField u := D.equation
  let i : Fin taylorLength := ⟨D.polynomial.natDegree, Nat.lt_succ_iff.mpr D.degree_le⟩
  have hi : u i = 1 := by
    simp [u, i, FreshCurve.coefficients, coefficientTuple, Polynomial.coeff_natDegree,
      D.monic.leadingCoeff]
  have hu : ratios u i = u := by funext j; simp [ratios, hi]
  have hv₀ : v 0 ≠ 0 := jet_zero_nonzero D 0 rfl
  have hgen : ratioField GeoField u i = ⊤ := by
    rw [ratioField, hu]
    exact D.generates
  obtain ⟨hpositive, hsource⟩ :=
    projective_height GeoField D.Fresh _ D.freshCurve hdiv u i (by simp [hi])
  have hpos : 0 < tupleHeight GeoField D.Fresh u := by
    rw [← hu]
    exact hpositive.mp (by rw [hu]; exact D.nonconstant)
  have hs : (tupleHeight GeoField D.Fresh u : ℚ) = affineDegree (extendIdeal R) := by
    have h := (hsource (by simpa only [hu] using hpos)).2
    rwa [hu, hgen, IntermediateField.finrank_top, Nat.cast_one, one_mul, ← hcone] at h
  have hcmp := height_comparison D hshort hdiv
  have hjpos : 0 < tupleHeight GeoField D.Fresh (ratios v 0) := by
    change 2 * tupleHeight GeoField D.Fresh u ≤ 133387 * tupleHeight GeoField D.Fresh
      (ratios v 0) at hcmp
    omega
  have himage : coneIdeal GeoField v = freshImage R := by
    rw [freshImage, D.equation]
    change RingHom.ker (coneEval GeoField v) =
      (RingHom.ker (coneEval GeoField u)).comap freshJetMap
    rw [RingHom.comap_ker, cone_eval_jets D]
  have hrank := K1_13_6_3_5_3_4.proof GeoField D.Fresh _ _ u i v 0 freshJetMap (by simp [hi]) hv₀ hgen
    (cone_eval_jets D)
  rw [← hcone] at hrank
  obtain ⟨hdim', ht⟩ := (projective_height GeoField D.Fresh _ D.freshCurve hdiv v 0 hv₀).2 hjpos
  rw [himage, ← hrank] at ht
  refine ⟨himage ▸ hdim', ?_⟩
  have hcmp' : 2 * (tupleHeight GeoField D.Fresh u : ℚ) ≤
      133387 * (tupleHeight GeoField D.Fresh (ratios v 0) : ℚ) := by exact_mod_cast hcmp
  rw [hs, ht] at hcmp'
  simpa only [mul_assoc] using hcmp'
end
end Low6966FatPad
end
section
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace Low6966FatPad
noncomputable section
open MvPolynomial K1_13_6 K1_13_6_3 K1_13_6_3_5
attribute [local instance] MvPolynomial.gradedAlgebra
private theorem boundary_support {A R : CoeffIdeal} (hs : ShortSupport A)
    (hR : boundaryIdeal A ≤ R) : ShortSupport R := by
  intro i hi
  apply hR
  apply Ideal.subset_span
  refine ⟨MvPolynomial.X i, hs i hi, ?_⟩
  rw [totalDegree_X]
  exact homogeneousComponent_eq_self (isHomogeneous_X _ i)
theorem padding (A : CoeffIdeal) (hA : A.IsPrime) (hAe : (extendIdeal A).IsPrime)
    (hdim : dimension A = 2) (hbir : FreshBirational A) (hs : ShortSupport A) :
    2 * affineDegree A ≤ 133387 * affineDegree (freshImage A) := by
  classical
  have h1 := K1_13_6_3_5_1.of_children K1_13_6_3_5_1_1.proof K1_13_6_3_5_1_2.proof
  have h2 := K1_13_6_3_5_2.proof
  have h4 := K1_13_6_3_5_4.proof
  have h5 := K1_13_6_3_5_5.of_children K1_13_6_3_5_5_1.proof K1_13_6_3_5_5_2.proof
    K1_13_6_3_5_5_3.proof K1_13_6_3_5_5_4.proof
  let B := extendIdeal A
  let C := freshImage A
  let S := (boundaryIdeal B).minimalPrimesFinset
  let T := (boundaryIdeal C).minimalPrimesFinset
  let image (P : Ideal FreshCoeffRing) : JetIdeal := P.comap freshJetMap
  let weight (P : Ideal FreshCoeffRing) : ℕ := boundaryWeight (boundaryIdeal B) P
  let rank (P : Ideal FreshCoeffRing) : ℕ := residueDegree freshJetMap P
  obtain ⟨hpoly, hdescend⟩ := h2 A hA
  have hdimB : dimension B = 2 :=
    (congrArg Polynomial.natDegree hpoly).trans hdim
  have hdegree : affineDegree A = affineDegree B := by
    change affineDegree A = affineDegree (extendIdeal A)
    simp only [affineDegree, hpoly]
  have hbirB : IsBirationalOn freshProjection B := hbir
  obtain ⟨hdimC, hproject⟩ := h4 _ _ _ freshProjection freshProjection_linear B hAe hdimB hbirB
  have hC : C.IsPrime := by
    let _ : B.IsPrime := hAe
    exact Ideal.IsPrime.comap freshJetMap
  have hdimC' : dimension C = 2 := hdimC
  have hheight (P : Ideal FreshCoeffRing) (hP : P ∈ S) :
      dimension (image P) = 2 ∧
      2 * affineDegree P ≤ 133387 * (rank P : ℚ) * affineDegree (image P) := by
    have hp := Ideal.mem_minimalPrimesFinset.mp hP
    obtain ⟨R, hR, rfl⟩ := hdescend P hp
    obtain ⟨hd, hhom⟩ := (h1 _ _ A hA hdim).1 R hR
    exact boundary_degree R hR.isPrime hp.isPrime hhom hd (boundary_support hs hR.le)
  have hmaps (P : Ideal FreshCoeffRing) (hP : P ∈ S) : image P ∈ T := by
    apply Ideal.mem_minimalPrimesFinset.mpr
    exact hproject P (Ideal.mem_minimalPrimesFinset.mp hP) (hheight P hP).1
  have hfibre (Q : JetIdeal) (hQ : Q ∈ T) :
      (∑ P ∈ S.filter (fun P => image P = Q), weight P * rank P) ≤
        boundaryWeight (boundaryIdeal C) Q := by
    exact h5 _ _ _ freshProjection freshProjection_linear B hAe hbirB Q
      (Ideal.mem_minimalPrimesFinset.mp hQ)
  calc
    2 * affineDegree A = 2 * ∑ P ∈ S, (weight P : ℚ) * affineDegree P := by
      rw [hdegree, (h1 _ _ B hAe hdimB).2]
    _ ≤ ∑ P ∈ S, 133387 * ((weight P * rank P : ℕ) : ℚ) * affineDegree (image P) := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro P hP
      push_cast
      calc
        2 * ((weight P : ℚ) * affineDegree P) =
            (weight P : ℚ) * (2 * affineDegree P) := by ring
        _ ≤ (weight P : ℚ) * (133387 * (rank P : ℚ) * affineDegree (image P)) :=
          mul_le_mul_of_nonneg_left (hheight P hP).2 (by positivity)
        _ = _ := by ring
    _ = ∑ Q ∈ T, ∑ P ∈ S.filter (fun P => image P = Q),
        133387 * ((weight P * rank P : ℕ) : ℚ) * affineDegree (image P) :=
      (Finset.sum_fiberwise_of_maps_to hmaps _).symm
    _ ≤ ∑ Q ∈ T, 133387 * (boundaryWeight (boundaryIdeal C) Q : ℚ) * affineDegree Q := by
      apply Finset.sum_le_sum
      intro Q hQ
      calc
        _ = ∑ P ∈ S.filter (fun P => image P = Q),
            133387 * ((weight P * rank P : ℕ) : ℚ) * affineDegree Q := by
          apply Finset.sum_congr rfl
          intro P hP
          rw [(Finset.mem_filter.mp hP).2]
        _ = 133387 * ((∑ P ∈ S.filter (fun P => image P = Q), weight P * rank P : ℕ) : ℚ) *
            affineDegree Q := by
          rw [Nat.cast_sum, Finset.mul_sum, Finset.sum_mul]
        _ ≤ _ := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (by exact_mod_cast hfibre Q hQ) (by positivity))
          (affineDegree_nonneg Q)
    _ = 133387 * affineDegree C := by
      rw [(h1 _ _ C hC hdimC').2, Finset.mul_sum]
      exact Finset.sum_congr rfl (fun _ _ => mul_assoc ..)
end
end Low6966FatPad
end

#print axioms Low6966FatPad.padding

end Merged6967_Low6966FatPad

section Merged6967_Low6966LeadingBase
set_option Elab.async false



set_option Elab.async false
set_option autoImplicit true
section
namespace Low6966Leading
noncomputable section
variable {top : Fin 16}
open P3 (K I)
open Low6966Prices (TrueWeightLE anchorCutoff taylorLength lowerWidth lowerIndex lowerTop)
open K1_13 (Row indexDegree)
open K1_13_5 (NodeFamily)
open K1_13 (Shape)
open scoped BigOperators Polynomial
abbrev lowBox : Shape := ⟨142, 58, 29⟩
abbrev graphBox (top : Fin 16) : Shape :=
  ⟨lowerWidth top, lowerIndex top + 1, (lowerIndex top + 1) / 2⟩
def liftedBox (top : Fin 16) (L : ℕ) : Shape :=
  let j := 2 + (L - 4) * (lowerIndex top + 2)
  ⟨1 + (L - 4) * lowerWidth top, j, min (1 + (L - 4) * (lowerTop top + 2)) (j / 2)⟩
def firstWidth (top : Fin 16) : ℕ :=
  max (lowerWidth top) ((2 * lowerTop top - 1) * lowerWidth top - lowerTop top ^ 2)
def firstIndex (top : Fin 16) : ℕ :=
  max (lowerIndex top) ((2 * lowerTop top - 1) * lowerIndex top - 2 * lowerTop top ^ 2)

structure FirstRow (top : Fin 16) (q : Row 2) : Prop where
  ne_zero : q ≠ 0
  total : q.totalDegree ≤ firstWidth top
  index : indexDegree q ≤ firstIndex top

structure FirstFactors (top : Fin 16) {n : ℕ} (f : Fin n → Row 2) : Prop where
  irreducible : ∀ i, Irreducible (f i)
  positive : ∀ i, 0 < (f i).degreeOf 1
  total : (∑ i, (f i).totalDegree) ≤ firstWidth top
  index : (∑ i, indexDegree (f i)) ≤ firstIndex top

structure SecondFactors (top : Fin 16) {n : ℕ} (f : Fin n → Row 3) : Prop where
  irreducible : ∀ i, Irreducible (f i)
  positive : ∀ i, 0 < (f i).degreeOf 2
  weight : ∀ i, TrueWeightLE (f i) anchorCutoff
  total : (∑ i, (f i).totalDegree) ≤ lowerWidth top
  index : (∑ i, indexDegree (f i)) ≤ lowerIndex top
  coordinate : (∑ i, (f i).degreeOf 2) ≤ lowerTop top
def Whole (f : Row 3) : Prop :=
  f ∣ K1_13_5.compatibilityNumerator f (taylorLength - 3)

-- Mixed volume coefficients in the support bounds of the contracted row.
def mixedCoefficients (top : Fin 16) : ℕ × ℕ × ℕ :=
  ![(95008609312727, 307728203568102, 3985398677344),
    (85694564317946, 297929327140401, 30078769),
    (76860899798513, 283726973092954, 4020982594106),
    (68507615754428, 273145254364667, 30345543),
    (60634712185691, 258124474366646, 4056566510868),
    (53242189092302, 246759913337773, 30612317),
    (46330046474261, 230920707389178, 4092150427630),
    (39898284331568, 218773304059719, 30879091),
    (33946902664223, 202115672160550, 4127734344392),
    (28475901472226, 189185426530505, 31145865),
    (23485280755577, 171709368680762, 4163318261154),
    (18975040514276, 157996280750131, 31412639),
    (14945180748323, 139701796949814, 4198902177916),
    (11395701457718, 125205866718597, 31679413),
    (8326602642461, 106092956967706, 4234486094678),
    (5737884302552, 90814184435903, 31946187)] top

def mixedBudget (top : Fin 16) : ℕ :=
  let (b, j, r) := mixedCoefficients top
  b * lowerWidth top + j * lowerIndex top + r * lowerTop top
def invariantBudget (top : Fin 16) : ℕ :=
  lowerWidth top * (1 + (2 * (taylorLength + 1) - 7) * (lowerWidth top - 1))
abbrev firstExponent : ℕ := 2 * taylorLength - 5
abbrev firstChartTotal (top : Fin 16) : ℕ := 1 + firstExponent * (firstWidth top - 1)
abbrev firstChartTop (top : Fin 16) : ℕ :=
  min (firstChartTotal top) (firstExponent * (firstIndex top - 1) + taylorLength - 1)
def firstMixedBudget (top : Fin 16) : ℕ :=
  firstWidth top * firstChartTop top + firstIndex top * (firstChartTotal top - firstChartTop top)
structure ProperCover (top : Fin 16) (w : I → K) (Γ : Finset K) (s : K → (Polynomial K)) where
  isolated : Finset K
  multiple : NodeFamily w Γ s
  invariant : NodeFamily w Γ s
  cover : Γ ⊆ isolated ∪ multiple.labels ∪ invariant.labels
  mixed : isolated.card + 2 * multiple.totalCap ≤ mixedBudget top
  fresh : invariant.totalCap ≤ (invariantBudget top)
  components : multiple.n + invariant.n ≤ 2 * (invariantBudget top)
end
end Low6966Leading
end
section
namespace Low6966Leading_1
noncomputable section
variable {top : Fin 16}
open K1_13 (Geom Row Shape atJet)
open K1_13_5 (RegularAt compatibilityNumerator separant)
open Low6966Leading (graphBox liftedBox)
open K1_13_5_4 (GeometricX GeoRow genericCoeff genericRow graph graphPoint
  InLiftedBox RepresentsOnGraph jetPoint regularLocus extendedAtJet)
open Low6966Prices (taylorLength physicalDegree)
open Low6966Leading (Whole mixedBudget)
open Polynomial
open scoped BigOperators
abbrev Coefficients := Fin taylorLength → GeometricX
abbrev CoefficientIdeal := Ideal (GeoRow taylorLength)
abbrev CurveIndex (n : ℕ) := Fin n × Ideal (GeoRow 3)
def coefficientPoint (S : (Polynomial Geom)) : Coefficients :=
  fun j => algebraMap Geom GeometricX (S.coeff j)
def coefficientPolynomial (a : Coefficients) : (Polynomial GeometricX) :=
  ∑ j : Fin taylorLength, Polynomial.monomial j.val (a j)
def oldCut (f : Row 3) : Row 3 := compatibilityNumerator f (taylorLength - 3)
def oldNext (f : Row 3) : Row 3 := compatibilityNumerator f (taylorLength - 2)
open K1_13_5_4_1 (compatibility_degree)
theorem ordinary_bound (f : Row 3) :
    (oldCut f).totalDegree ≤ 1 + (2 * (taylorLength + 1) - 7) * (f.totalDegree - 1) :=
  compatibility_degree f (taylorLength - 3)
def oldCutIdeal (f : Row 3) : Ideal (GeoRow 3) :=
  Ideal.span {genericRow f, genericRow (oldCut f)}
def properComponents {n : ℕ} (f : Fin n → Row 3) : Finset (CurveIndex n) := by
  classical
  exact Finset.univ.biUnion fun i =>
    if Whole (f i) then ∅ else
      ((oldCutIdeal (f i)).retainedMinimalPrimes (genericRow (separant (f i)))).image
        (fun P => (i, P))
theorem mem_properComponents {n : ℕ} {f : Fin n → Row 3} {i : Fin n}
    {P : Ideal (GeoRow 3)} : (i, P) ∈ properComponents f ↔
    ¬ Whole (f i) ∧ P ∈ (oldCutIdeal (f i)).retainedMinimalPrimes (genericRow (separant (f i))) := by
  classical
  simp only [properComponents, Finset.mem_biUnion, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨k, hk⟩
    by_cases hw : Whole (f k)
    · simp [hw] at hk
    · simp only [hw, ite_false] at hk
      obtain ⟨P', hP', he⟩ := Finset.mem_image.mp hk
      cases he
      exact ⟨hw, hP'⟩
  · rintro ⟨hw, hP⟩
    exact ⟨i, by simpa only [hw, ite_false] using Finset.mem_image.mpr ⟨P, hP, rfl⟩⟩
def componentLength (f : Row 3) (P : Ideal (GeoRow 3)) : ℕ∞ := by
  classical
  exact if hp : P.IsPrime then
    letI := hp
    let A := Localization.AtPrime P
    Module.length A (A ⧸ (oldCutIdeal f).map (algebraMap (GeoRow 3) A))
  else 0
def SimpleInvariant (f : Row 3) (P : Ideal (GeoRow 3)) : Prop :=
  componentLength f P = 1 ∧ genericRow (oldNext f) ∈ P
def nextCutLocus (f : Row 3) (P : Ideal (GeoRow 3)) : Set (Fin 3 → GeometricX) :=
  {y | y ∈ regularLocus f P ∧ MvPolynomial.eval y (genericRow (oldNext f)) = 0}
def reconstruct (f : Row 3) (numerator : Fin taylorLength → GeoRow 4)
    (y : Fin 3 → GeometricX) : Coefficients :=
  fun i => MvPolynomial.eval (graphPoint f y) (numerator i) /
    MvPolynomial.eval y (genericRow (separant f)) ^ (taylorLength - 4)
structure LiftedChart (top : Fin 16) (f : Row 3) where
  cut : GeoRow 4
  next : GeoRow 4
  numerator : Fin taylorLength → GeoRow 4
  graph_box : InLiftedBox (graph f) (graphBox top) 1
  cut_box : InLiftedBox cut (liftedBox top (taylorLength + 1)) (taylorLength - 1)
  next_box : InLiftedBox next (liftedBox top (taylorLength + 2)) taylorLength
  coefficient_box : ∀ i, InLiftedBox (numerator i) (liftedBox top taylorLength) (taylorLength - 2)
  cut_represents : RepresentsOnGraph f (oldCut f) cut
  next_represents : RepresentsOnGraph f (oldNext f) next
  actual : ∀ S : (Polynomial Geom), S.natDegree ≤ physicalDegree → RegularAt 2 f S →
    atJet (oldCut f) S = 0 ∧ atJet (oldNext f) S = 0 ∧
      reconstruct f numerator (jetPoint S) = coefficientPoint S
structure MixedSections (top : Fin 16) {n : ℕ} (f : Fin n → Row 3) (T : ∀ i, LiftedChart top (f i)) where
  length : CurveIndex n → ℕ
  degree : CurveIndex n → ℕ
  length_eq : ∀ a ∈ properComponents f, (length a : ℕ∞) = componentLength (f a.1) a.2
  length_pos : ∀ a ∈ properComponents f, 0 < length a
  total : (∑ a ∈ properComponents f, length a * degree a) ≤ mixedBudget top
  points : ∀ a ∈ properComponents f, genericRow (oldNext (f a.1)) ∉ a.2 →
    (nextCutLocus (f a.1) a.2).Finite ∧ (nextCutLocus (f a.1) a.2).ncard ≤ degree a
  curves : ∀ a ∈ properComponents f, 2 ≤ length a →
    ∃ Q : CoefficientIdeal, Q.IsPrime ∧ (MvPolynomial.affineHilbertPolynomial Q).natDegree ≤ 1 ∧
      0 < degree a ∧ MvPolynomial.affineDegree Q ≤ (degree a : ℚ) ∧
      ∀ y ∈ regularLocus (f a.1) a.2,
        reconstruct (f a.1) (T a.1).numerator y ∈ MvPolynomial.zeroLocus GeometricX Q
structure ActualSolutionCurve (f : Row 3) (Q : CoefficientIdeal) : Prop where
  prime : Q.IsPrime
  dimension : (MvPolynomial.affineHilbertPolynomial Q).natDegree = 1
  solves : ∀ a ∈ MvPolynomial.zeroLocus GeometricX Q,
    extendedAtJet f (coefficientPolynomial a) = 0
  regular : ∃ a ∈ MvPolynomial.zeroLocus GeometricX Q,
    extendedAtJet (separant f) (coefficientPolynomial a) ≠ 0
end
end Low6966Leading_1
end
section
set_option maxRecDepth 6000
set_option maxHeartbeats 1000000
namespace Low6966Leading
noncomputable section
variable {top : Fin 16}
open P3 (I K node)
open Low6966Prices (Messages)
open K1_13_5 (NodeCapacity NodeFamily)
open Polynomial ProximityPrize.Benchmark
open scoped BigOperators
theorem agree_pair_le {w Γ s} (h : Messages w Γ s)
    {γ η : K} (hγ : γ ∈ Γ) (hη : η ∈ Γ) (hne : γ ≠ η)
    (sites : Finset I)
    (hγval : ∀ i ∈ sites, (s γ).eval (node i) = w i)
    (hηval : ∀ i ∈ sites, (s η).eval (node i) = w i) :
    sites.card ≤ 133387 := by
  classical
  let diff := s γ - s η
  have hdiff : diff ≠ 0 := sub_ne_zero.mpr (fun heq => hne (h.distinct hγ hη heq))
  have hdeg : diff.natDegree ≤ 133387 :=
    (Polynomial.natDegree_sub_le _ _).trans (max_le (h.degree γ hγ) (h.degree η hη))
  have hroots : (sites.image node).card ≤ diff.natDegree := by
    apply Polynomial.card_le_degree_of_subset_roots
    intro a ha
    change a ∈ sites.image node at ha
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
    exact (Polynomial.mem_roots hdiff).mpr (by simp [diff, hγval i hi, hηval i hi])
  rw [Finset.card_image_of_injective _ IRSProfile.domain.injective] at hroots
  exact hroots.trans hdeg
private theorem count_by_nodes {α ι : Type*} [Fintype ι] [DecidableEq ι] (T : Finset α)
    (S : α → Finset ι) {a d : ℕ}
    (hsize : ∀ γ ∈ T, a ≤ (S γ).card)
    (hcap : ∀ i : ι, (T.filter fun γ => i ∈ S γ).card ≤ d) :
    T.card * a ≤ Fintype.card ι * d := by
  classical
  calc
    T.card * a = ∑ _ ∈ T, a := by simp
    _ ≤ ∑ γ ∈ T, (S γ).card := Finset.sum_le_sum hsize
    _ = ∑ γ ∈ T, ∑ i : ι, if i ∈ S γ then (1 : ℕ) else 0 := by
      apply Finset.sum_congr rfl
      intro γ _
      rw [Finset.sum_boole]
      congr 1
      ext i
      simp
    _ = ∑ i : ι, ∑ γ ∈ T, if i ∈ S γ then (1 : ℕ) else 0 := Finset.sum_comm
    _ = ∑ i : ι, (T.filter fun γ => i ∈ S γ).card := by simp
    _ ≤ ∑ _ : ι, d := Finset.sum_le_sum fun i _ => hcap i
    _ = Fintype.card ι * d := by simp
theorem nodeCapacity_count {w Γ s d} (h : Messages w Γ s)
    (hc : NodeCapacity w Γ s d) : 46372 * Γ.card ≤ 82385 * d + 46372 := by
  classical
  by_cases hsmall : Γ.card ≤ 1
  · omega
  obtain ⟨persistent, hp, hd⟩ := hc
  obtain ⟨γ, hγ, η, hη, hne⟩ := Finset.one_lt_card.mp (by omega : 1 < Γ.card)
  have hpN := agree_pair_le h hγ hη hne persistent
    (fun i hi => hp i hi γ hγ) (fun i hi => hp i hi η hη)
  let U : Finset I := Finset.univ \ persistent
  let hits (γ : K) : Finset I := Finset.univ.filter fun i => (s γ).eval (node i) = w i
  let supports (γ : K) : Finset U := (hits γ \ persistent).subtype (· ∈ U)
  let a : ℕ := 179759 - persistent.card
  let b : ℕ := 133387 - persistent.card
  have hU : Fintype.card U = 262144 - persistent.card := by
    rw [Fintype.card_coe]
    change (Finset.univ \ persistent).card = _
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ persistent), Finset.card_univ]
    change Fintype.card (Fin (2 ^ 18)) - persistent.card = _
    rw [Fintype.card_fin]
    rfl
  have hsubcard (T : Finset I) : ((T \ persistent).subtype (· ∈ U)).card =
      (T \ persistent).card := by
    rw [Finset.card_subtype, Finset.filter_true_of_mem]
    intro i hi
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, (Finset.mem_sdiff.mp hi).2⟩
  have hpSub : ∀ γ ∈ Γ, persistent ⊆ hits γ := by
    intro γ hγ i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp i hi γ hγ⟩
  have hsize : ∀ γ ∈ Γ, a ≤ (supports γ).card := by
    intro γ hγ
    obtain ⟨T, hT, hval⟩ := h.hits γ hγ
    have hTsub : T ⊆ hits γ := fun i hi => Finset.mem_filter.mpr ⟨Finset.mem_univ _, hval i hi⟩
    calc
      a ≤ (hits γ).card - persistent.card := Nat.sub_le_sub_right
        (hT.trans (Finset.card_le_card hTsub)) _
      _ = (supports γ).card := by
        dsimp only [supports]
        rw [hsubcard, Finset.card_sdiff_of_subset (hpSub γ hγ)]
  have hpair : ∀ γ ∈ Γ, ∀ η ∈ Γ, γ ≠ η →
      (supports γ ∩ supports η).card ≤ b := by
    intro γ hγ η hη hne
    have heq : supports γ ∩ supports η =
        ((hits γ ∩ hits η) \ persistent).subtype (· ∈ U) := by
      ext i
      simp only [supports, Finset.mem_inter, Finset.mem_subtype, Finset.mem_sdiff]
      exact ⟨fun h => ⟨⟨h.1.1, h.2.1⟩, h.1.2⟩,
        fun h => ⟨⟨h.1.1, h.2⟩, ⟨h.1.2, h.2⟩⟩⟩
    have hsub : persistent ⊆ hits γ ∩ hits η :=
      fun _ hi => Finset.mem_inter.mpr ⟨hpSub γ hγ hi, hpSub η hη hi⟩
    rw [heq, hsubcard, Finset.card_sdiff_of_subset hsub]
    apply Nat.sub_le_sub_right
    exact agree_pair_le h hγ hη hne _
      (fun i hi => (Finset.mem_filter.mp (Finset.mem_inter.mp hi).1).2)
      (fun i hi => (Finset.mem_filter.mp (Finset.mem_inter.mp hi).2).2)
  have hcap : ∀ i : U, (Γ.filter fun γ => i ∈ supports γ).card ≤ d := by
    intro i
    have hi := (Finset.mem_sdiff.mp i.property).2
    apply (Finset.card_le_card ?_).trans (hd i.val hi)
    intro γ hγ
    obtain ⟨hγΓ, hγi⟩ := Finset.mem_filter.mp hγ
    exact Finset.mem_filter.mpr
      ⟨hγΓ, (Finset.mem_filter.mp (Finset.mem_sdiff.mp (Finset.mem_subtype.mp hγi)).1).2⟩
  have hincNat := count_by_nodes Γ supports hsize hcap
  let l : ℤ := Γ.card
  let x : ℤ := a
  have hb : (b : ℤ) = x - 46372 := by
    dsimp [b, x, a]
    push_cast [Nat.cast_sub hpN, Nat.cast_sub (hpN.trans (by decide : 133387 ≤ 179759))]
    ring
  have hu : (Fintype.card U : ℤ) = x + 82385 := by
    rw [hU]
    dsimp [x, a]
    push_cast [Nat.cast_sub (hpN.trans (by decide : 133387 ≤ 262144)),
      Nat.cast_sub (hpN.trans (by decide : 133387 ≤ 179759))]
    ring
  have hinc' : l * x ≤ (x + 82385) * (d : ℤ) := by
    rw [← hu]
    dsimp only [l, x]
    exact_mod_cast hincNat
  have hinc : (l - (d : ℤ)) * x ≤ 82385 * d := by nlinarith only [hinc']
  by_contra! hbadNat
  have hbad : 82385 * (d : ℤ) < (l - 1) * 46372 := by
    have hc : 82385 * (d : ℤ) + 46372 < 46372 * l := by
      dsimp only [l]
      exact_mod_cast hbadNat
    linarith only [hc]
  have hd0 : (0 : ℤ) ≤ d := Int.natCast_nonneg _
  have hl0 : (0 : ℤ) < l := by
    dsimp [l]
    exact_mod_cast (show 0 < Γ.card by omega)
  have hk : 0 < l - (d : ℤ) := by linarith only [hbad, hd0]
  have hcoef : 36013 * (d : ℤ) < (l - (d : ℤ)) * 46372 := by linarith only [hbad]
  have hden : 0 < 82385 * 46372 - 36013 * x := by
    have hle := mul_le_mul_of_nonneg_left hinc (by decide : (0 : ℤ) ≤ 36013)
    have hlt := mul_lt_mul_of_pos_right hcoef (by decide : (0 : ℤ) < 82385)
    have hpos : 0 < (l - (d : ℤ)) * (82385 * 46372 - 36013 * x) := by
      nlinarith only [hle, hlt]
    exact pos_of_mul_pos_right hpos hk.le
  have hdenNat : Fintype.card U * b < a * a := by
    have hi : (Fintype.card U : ℤ) * (b : ℤ) < x * x := by
      rw [hu, hb]
      nlinarith only [hden]
    dsimp only [x] at hi
    exact_mod_cast hi
  have hba : b ≤ a := Nat.sub_le_sub_right (by decide : 133387 ≤ 179759) _
  have hj := Finset.card_mul_sq_sub_card_mul_le_of_inter_card_le
    Γ supports a b hsize hpair
  have hjInt : l * ((a * a - Fintype.card U * b : ℕ) : ℤ) ≤
      (Fintype.card U : ℤ) * ((a - b : ℕ) : ℤ) := by
    dsimp only [l]
    exact_mod_cast hj
  push_cast [Nat.cast_sub hba, Nat.cast_sub hdenNat.le] at hjInt
  rw [hu, hb] at hjInt
  have hj' : (l - 1) * 82385 * 46372 ≤ (36013 * l + 46372) * x := by
    nlinarith only [hjInt]
  have hle := mul_le_mul_of_nonneg_left hj' hk.le
  have hle' := mul_le_mul_of_nonneg_left hinc
    (show 0 ≤ 36013 * l + 46372 by linarith only [hl0])
  have hpos := mul_lt_mul_of_pos_left hbad
    (show 0 < 82385 * l by linarith only [hl0])
  nlinarith only [hle, hle', hpos]
theorem nodeFamily_count {w Γ s} (C : NodeFamily w Γ s) (h : Messages w Γ s) :
    46372 * C.labels.card ≤ 82385 * C.totalCap + 46372 * C.n := by
  classical
  calc
    46372 * C.labels.card ≤ 46372 * ∑ i, (C.part i).card :=
      Nat.mul_le_mul_left _ Finset.card_biUnion_le
    _ = ∑ i, 46372 * (C.part i).card := by rw [Finset.mul_sum]
    _ ≤ ∑ i, (82385 * C.cap i + 46372) := by
      exact Finset.sum_le_sum fun i _ => nodeCapacity_count (h.mono (C.sub i)) (C.localCapacity i)
    _ = 82385 * C.totalCap + 46372 * C.n := by
      simp [NodeFamily.totalCap, Finset.sum_add_distrib, Finset.mul_sum, Nat.mul_comm]
end
end Low6966Leading
end
section
namespace Low6966Leading_1
noncomputable section
variable {top : Fin 16}
open P3 (I K node)
open Low6966Prices (Messages taylorLength physicalDegree)
open Low6966Leading (nodeCapacity_count)
open K1_13 (Geom embed extend)
open K1_13_5 (NodeCapacity)
open K1_13_5_4 (GeometricX GeoRow)
open Polynomial
open scoped BigOperators
private theorem recover_coefficients (S : (Polynomial Geom)) (hS : S.natDegree ≤ physicalDegree) :
    coefficientPolynomial (coefficientPoint S) = S.map (algebraMap Geom GeometricX) := by
  unfold coefficientPolynomial coefficientPoint
  rw [Fin.sum_univ_eq_sum_range (fun j =>
    Polynomial.monomial j (algebraMap Geom GeometricX (S.coeff j)))]
  conv_rhs => rw [Polynomial.as_sum_range' S taylorLength (Nat.lt_succ_of_le hS)]
  simp only [Polynomial.map_sum, Polynomial.map_monomial]
private theorem coefficientPoint_injOn {w Γ s} (h : Messages w Γ s) :
    Set.InjOn (fun γ => coefficientPoint (extend (s γ))) (Γ : Set K) := by
  intro γ hγ δ hδ heq
  apply h.distinct hγ hδ
  apply Polynomial.map_injective embed embed.injective
  apply Polynomial.map_injective (algebraMap Geom GeometricX) (algebraMap Geom GeometricX).injective
  have hdeg : ∀ η ∈ Γ, (extend (s η)).natDegree ≤ physicalDegree := by
    intro η hη
    simpa only [Polynomial.natDegree_map] using h.degree η hη
  rw [← recover_coefficients _ (hdeg _ hγ), ← recover_coefficients _ (hdeg _ hδ)]
  exact congrArg coefficientPolynomial heq
private def valueCut (x y : GeometricX) : GeoRow taylorLength :=
  (∑ j : Fin taylorLength, MvPolynomial.C (x ^ j.val) * MvPolynomial.X j) - MvPolynomial.C y
private theorem totalDegree_valueCut (x y : GeometricX) : (valueCut x y).totalDegree ≤ 1 := by
  unfold valueCut
  apply (MvPolynomial.totalDegree_sub_C_le _ _).trans
  apply MvPolynomial.totalDegree_finsetSum_le
  intro j _
  simpa only [MvPolynomial.totalDegree_C, zero_add, MvPolynomial.totalDegree_X] using
    MvPolynomial.totalDegree_mul (MvPolynomial.C (x ^ j.val)) (MvPolynomial.X j)
private theorem eval_valueCut (a : Coefficients) (x y : GeometricX) :
    MvPolynomial.eval a (valueCut x y) = (coefficientPolynomial a).eval x - y := by
  simp only [valueCut, coefficientPolynomial, map_sub, map_sum, map_mul, MvPolynomial.eval_C,
    MvPolynomial.eval_X, Polynomial.eval_finsetSum, Polynomial.eval_monomial]
  exact congrArg (fun z : GeometricX => z - y) (Finset.sum_congr rfl fun _ _ => mul_comm _ _)
private def constantEmbed : K →+* GeometricX := (algebraMap Geom GeometricX).comp embed
private def nodeCut (w : I → K) (i : I) : GeoRow taylorLength :=
  valueCut (constantEmbed (node i)) (constantEmbed (w i))
private theorem eval_nodeCut_iff {w Γ s} (h : Messages w Γ s) {γ : K} (hγ : γ ∈ Γ) (i : I) :
    MvPolynomial.eval (coefficientPoint (extend (s γ))) (nodeCut w i) = 0 ↔
      (s γ).eval (node i) = w i := by
  have hdeg : (extend (s γ)).natDegree ≤ physicalDegree := by
    simpa only [Polynomial.natDegree_map] using h.degree γ hγ
  rw [nodeCut, eval_valueCut, recover_coefficients _ hdeg, sub_eq_zero]
  unfold constantEmbed
  simp only [RingHom.comp_apply, Polynomial.eval_map_apply]
  exact (algebraMap Geom GeometricX).injective.eq_iff.trans embed.injective.eq_iff
theorem nodeCapacity_of_coefficient_curve {w Γ s} {d : ℕ} (h : Messages w Γ s)
    (Q : CoefficientIdeal) (hp : Q.IsPrime)
    (hdim : (MvPolynomial.affineHilbertPolynomial Q).natDegree ≤ 1)
    (hdegree : MvPolynomial.affineDegree Q ≤ (d : ℚ))
    (hcurve : ∀ γ ∈ Γ, coefficientPoint (extend (s γ)) ∈ MvPolynomial.zeroLocus GeometricX Q) :
    NodeCapacity w Γ s d := by
  classical
  let A := fun γ => coefficientPoint (extend (s γ))
  have hinj : Set.InjOn A (Γ : Set K) := coefficientPoint_injOn h
  by_cases hzero : (MvPolynomial.affineHilbertPolynomial Q).natDegree = 0
  · have bound := MvPolynomial.finite_zeroLocus_and_ncard_le_affineDegree (K := GeometricX) Q hzero
    have hsub : (↑(Γ.image A) : Set Coefficients) ⊆ MvPolynomial.zeroLocus GeometricX Q := by
      intro a ha
      obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp ha
      exact hcurve γ hγ
    have hcard := Set.ncard_le_ncard hsub bound.1
    rw [Set.ncard_coe_finset, Finset.card_image_of_injOn hinj] at hcard
    have hcard' : (Γ.card : ℚ) ≤ d := (Nat.cast_le.mpr hcard).trans (bound.2.trans hdegree)
    refine ⟨∅, by simp, fun i _ => (Finset.card_filter_le _ _).trans ?_⟩
    exact_mod_cast hcard'
  have hone : (MvPolynomial.affineHilbertPolynomial Q).natDegree = 1 := by omega
  let persistent := Finset.univ.filter fun i => nodeCut w i ∈ Q
  refine ⟨persistent, ?_, ?_⟩
  · intro i hi γ hγ
    have he := hcurve γ hγ (nodeCut w i) (Finset.mem_filter.mp hi).2
    exact (eval_nodeCut_iff h hγ i).mp he
  · intro i hi
    let cut := nodeCut w i
    have hcut : cut ∉ Q := fun hc => hi (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc⟩)
    let J := Q ⊔ Ideal.span {cut}
    have hJ := MvPolynomial.principalCut_natDegree_affineHilbertPolynomial_le_and_coeff_le_of_isPrime
      hp hcut (totalDegree_valueCut (constantEmbed (node i)) (constantEmbed (w i)))
    have hjdim : (MvPolynomial.affineHilbertPolynomial J).natDegree = 0 := by
      rw [hone] at hJ
      exact Nat.eq_zero_of_le_zero hJ.1
    have hjdeg : MvPolynomial.affineDegree J ≤ MvPolynomial.affineDegree Q := by
      rw [MvPolynomial.affineDegree_of_natDegree_eq_zero hjdim, MvPolynomial.affineDegree, hone]
      simpa [hone] using hJ.2
    have bound := MvPolynomial.finite_zeroLocus_and_ncard_le_affineDegree (K := GeometricX) J hjdim
    let selected := Γ.filter (fun γ => (s γ).eval (node i) = w i)
    have hsub : (↑(selected.image A) : Set Coefficients) ⊆ MvPolynomial.zeroLocus GeometricX J := by
      intro a ha
      obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp ha
      obtain ⟨hγ, he⟩ := Finset.mem_filter.mp hγ
      exact MvPolynomial.mem_zeroLocus_sup_span_singleton_iff.mpr
        ⟨hcurve γ hγ, (eval_nodeCut_iff h hγ i).mpr he⟩
    have hcard := Set.ncard_le_ncard hsub bound.1
    rw [Set.ncard_coe_finset, Finset.card_image_of_injOn (hinj.mono (Finset.filter_subset _ _))] at hcard
    have hcard' : (selected.card : ℚ) ≤ d :=
      (Nat.cast_le.mpr hcard).trans (bound.2.trans (hjdeg.trans hdegree))
    exact_mod_cast hcard'
theorem curveCount_le_twice_degree {w Γ s} {d : ℕ} (h : Messages w Γ s) (hd : 0 < d)
    (hc : NodeCapacity w Γ s d) : Γ.card ≤ 2*d := by
  have hcount := nodeCapacity_count h hc
  omega
end
end Low6966Leading_1
end
section
namespace Low6966Leading_1
noncomputable section
variable {top : Fin 16}
open Low6966Prices (physicalDegree taylorLength)
open Low6966Leading (SecondFactors)
open K1_13 (Geom Row atJet indexDegree)
open K1_13_5 (RegularAt separant)
open Low6966Leading (graphBox liftedBox)
open K1_13_5_4 (GeometricX GeoRow InLiftedBox RepresentsOnGraph graph genericCoeff genericRow jetPoint)
open K1_13_5_4_1 (liftRaw liftSep graphRaw thirdVelocityNumerator thirdNumerator
  padJet jetNumerator centre partialFlow_lift generic_graph eval_genericRow graphPoint_of_actual)
open K1_13_7_1 (weight_const_mul_le weight_X_le)
open MvPolynomial
open Polynomial (hasseDeriv)
open scoped BigOperators Polynomial
open K1_13_5_4_1_1 (mul_bound partialFlow_bound liftSep_eq liftedStep_bound generic_bound totalWeight indexWeight topWeight heightWeight lift_weight fits)
open K1_13_5_4_1_2 (represents)
open K1_13_5_4_1 (atJet_padJet taylor_coefficients_aux genericCoeff_ne_zero third_atJet_zero actual_zero_of_represents)
local notation "W" => weightedTotalDegree
private def coefficientNumerator (m : ℕ) (f : Row 3) (i : Fin m) : GeoRow 4 :=
  ∑ j : Fin m, MvPolynomial.C (((Polynomial.X - Polynomial.C centre) ^ j.val).coeff i.val) *
    genericRow (padJet f (m - 4) j.val)
private def cut (m : ℕ) (f : Row 3) : GeoRow 4 := genericRow (thirdNumerator f (m - 3))
private def next (m : ℕ) (f : Row 3) : GeoRow 4 := genericRow (thirdNumerator f (m - 2))
private theorem padded_bound (w : Fin 4 → ℕ) {initial step m : ℕ} {f : Row 3}
    (hinit : ∀ i, w i ≤ initial) (hs : W w (liftSep f) ≤ step)
    (hthird : ∀ k, W w (thirdNumerator f k) ≤ w 3 + k * step) (j : Fin m) :
    W w (padJet f (m - 4) j.val) ≤ initial + (m - 4) * step := by
  unfold padJet jetNumerator
  have hpow := (weightedTotalDegree_pow_le w (liftSep f) (m - 4 - (j.val - 3))).trans
    (Nat.mul_le_mul_left _ hs)
  split_ifs with hj
  · have hz : j.val - 3 = 0 := by omega
    rw [hz, Nat.sub_zero] at hpow ⊢
    exact (mul_bound hpow ((weight_X_le w _).trans (hinit _))).trans_eq (Nat.add_comm _ _)
  · have hsum : (m - 4 - (j.val - 3)) + (j.val - 3) = m - 4 := by
      have hj' := j.isLt
      omega
    calc
      _ ≤ (m - 4 - (j.val - 3)) * step + (w 3 + (j.val - 3) * step) :=
        mul_bound hpow ((weight_const_mul_le w _ _).trans (hthird _))
      _ = w 3 + ((m - 4 - (j.val - 3)) + (j.val - 3)) * step := by ring
      _ ≤ _ := by rw [hsum]; exact Nat.add_le_add_right (hinit 3) _
private theorem weight_bounds (w : Fin 4 → ℕ) (base delta step initial m : ℕ) {f : Row 3}
    (hf : W w (liftRaw f) ≤ base)
    (hshift : ∀ i : Fin 3, w i.succ ≤ w i.castSucc + delta)
    (hsep : base - w 2 + delta ≤ step) (hvelocity : base + 2 * delta ≤ w 3 + step)
    (hinit : ∀ i, w i ≤ initial) :
    W w (graph f) ≤ base + delta ∧
    (∀ k, W w (genericRow (thirdNumerator f k)) ≤ w 3 + k * step) ∧
    (∀ i, W w (coefficientNumerator m f i) ≤ initial + (m - 4) * step) := by
  have hg : W w (graphRaw f) ≤ base + delta := by
    rw [← partialFlow_lift]
    exact K1_13_5_4_1_1.partialFlow_bound w hshift hf
  have hs : W w (liftSep f) ≤ base - w 2 := by
    rw [liftSep_eq]
    exact (weightedTotalDegree_pderiv_le_sub w 2 _).trans (Nat.sub_le_sub_right hf _)
  have hu : W w (thirdVelocityNumerator f) ≤ w 3 + step := by
    unfold thirdVelocityNumerator
    exact ((weight_const_mul_le w _ _).trans (K1_13_5_4_1_1.partialFlow_bound w hshift hg)).trans (by omega)
  have hthird (k : ℕ) : W w (thirdNumerator f k) ≤ w 3 + k * step := by
    induction k with
    | zero =>
      simpa only [thirdNumerator, Nat.zero_mul, Nat.add_zero] using weight_X_le (R := (Polynomial Geom)) w 3
    | succ k ih =>
      rw [thirdNumerator, Nat.succ_mul, ← Nat.add_assoc]
      exact liftedStep_bound w hshift ih hs hsep hu k
  refine ⟨?_, fun k => (generic_bound w _).trans (hthird k), ?_⟩
  · rw [← generic_graph]
    exact (generic_bound w _).trans hg
  · intro i
    unfold coefficientNumerator
    apply mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mp
    apply Submodule.sum_mem
    intro j _
    exact mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mpr
      ((weight_const_mul_le w _ _).trans ((generic_bound w _).trans
        (padded_bound w hinit (hs.trans ((Nat.le_add_right _ _).trans hsep)) hthird j)))
private theorem fits_lifted {p : GeoRow 4} (L : ℕ)
    (hb : W totalWeight p ≤ 1 + (L - 4) * (Low6966Prices.lowerWidth top))
    (hj : W indexWeight p ≤ 2 + (L - 4) * (Low6966Prices.lowerIndex top + 2))
    (ht : W topWeight p ≤ 1 + (L - 4) * (Low6966Prices.lowerTop top + 2))
    (hh : W heightWeight p ≤ L - 2) :
    InLiftedBox p (liftedBox top L) (L - 2) :=
  fits hb hj ht hh
private theorem support (f : Row 3)
    (hb : f.totalDegree ≤ (Low6966Prices.lowerWidth top)) (hj : indexDegree f ≤ (Low6966Prices.lowerIndex top)) (ht : f.degreeOf 2 ≤ (Low6966Prices.lowerTop top)) :
    InLiftedBox (graph f) (graphBox top) 1 ∧
    InLiftedBox (cut taylorLength f) (liftedBox top (taylorLength + 1)) (taylorLength - 1) ∧
    InLiftedBox (next taylorLength f) (liftedBox top (taylorLength + 2)) taylorLength ∧
    ∀ i, InLiftedBox (coefficientNumerator taylorLength f i) (liftedBox top taylorLength) (taylorLength - 2) := by
  have htotal : W totalWeight (liftRaw f) ≤ (Low6966Prices.lowerWidth top) := by
    rw [lift_weight, show totalWeight ∘ Fin.castSucc = (1 : Fin 3 → ℕ) from by
      funext i; fin_cases i <;> decide, weightedTotalDegree_one]
    exact hb
  have hindex : W indexWeight (liftRaw f) ≤ (Low6966Prices.lowerIndex top) := by
    rw [lift_weight, show indexWeight ∘ Fin.castSucc = (Fin.val : Fin 3 → ℕ) from by
      funext i; fin_cases i <;> decide, ← K1_13_1.indexDegree_eq]
    exact hj
  have htop : W topWeight (liftRaw f) ≤ (Low6966Prices.lowerTop top) := by
    rw [lift_weight, show topWeight ∘ Fin.castSucc = Pi.single (2 : Fin 3) 1 from by
      funext i; fin_cases i <;> decide, weightedTotalDegree_piSingle]
    exact ht
  have hheight : W heightWeight (liftRaw f) ≤ 0 := by
    rw [lift_weight, show heightWeight ∘ Fin.castSucc = (0 : Fin 3 → ℕ) from by
      funext i; fin_cases i <;> decide, weightedTotalDegree, Finset.sup_le_iff]
    intro a _
    simp [Finsupp.weight_eq_sum]
  obtain ⟨bg, bn, bc⟩ := weight_bounds totalWeight (Low6966Prices.lowerWidth top) 0 (Low6966Prices.lowerWidth top) 1 taylorLength htotal
    (by intro i; fin_cases i <;> decide) (by fin_cases top <;> decide) (by fin_cases top <;> decide)
    (by intro i; fin_cases i <;> decide)
  obtain ⟨jg, jn, jc⟩ := weight_bounds indexWeight (Low6966Prices.lowerIndex top) 1 (Low6966Prices.lowerIndex top + 2) 2 taylorLength hindex
    (by intro i; fin_cases i <;> decide) (by fin_cases top <;> decide) (by fin_cases top <;> decide)
    (by intro i; fin_cases i <;> decide)
  obtain ⟨tg, tn, tc⟩ := weight_bounds topWeight (Low6966Prices.lowerTop top) 1 (Low6966Prices.lowerTop top + 2) 1 taylorLength htop
    (by intro i; fin_cases i <;> decide) (by fin_cases top <;> decide) (by fin_cases top <;> decide)
    (by intro i; fin_cases i <;> decide)
  obtain ⟨hg, hn, hc⟩ := weight_bounds heightWeight 0 1 1 1 taylorLength hheight
    (by intro i; fin_cases i <;> decide) (by fin_cases top <;> decide) (by fin_cases top <;> decide)
    (by intro i; fin_cases i <;> decide)
  have hrepl : min (Low6966Prices.lowerTop top + 1) ((Low6966Prices.lowerIndex top + 1) / 2) =
      (Low6966Prices.lowerIndex top + 1) / 2 := by fin_cases top <;> decide
  have hGraphB : W totalWeight (graph f) ≤ Low6966Prices.lowerWidth top := bg
  have hGraphH : W heightWeight (graph f) ≤ 1 := hg
  refine ⟨by simpa only [graphBox, hrepl] using fits hGraphB jg tg hGraphH, ?_, ?_, ?_⟩
  · rw [show taylorLength - 1 = taylorLength + 1 - 2 by decide]
    exact fits_lifted _ ((bn (taylorLength - 3)).trans (by fin_cases top <;> decide))
      ((jn (taylorLength - 3)).trans (by fin_cases top <;> decide))
      ((tn (taylorLength - 3)).trans (by fin_cases top <;> decide))
      ((hn (taylorLength - 3)).trans (by decide))
  · have hh : taylorLength + 2 - 2 = taylorLength := by decide
    simpa only [hh, next] using fits_lifted (taylorLength + 2) ((bn (taylorLength - 2)).trans (by fin_cases top <;> decide))
      ((jn (taylorLength - 2)).trans (by fin_cases top <;> decide))
      ((tn (taylorLength - 2)).trans (by fin_cases top <;> decide))
      ((hn (taylorLength - 2)).trans (by decide))
  · intro i
    exact fits_lifted _ (bc i) (jc i) (tc i) ((hc i).trans (by decide))
private theorem atJet_padded (f : Row 3) (S : (Polynomial Geom)) (hf : atJet f S = 0)
    {m : ℕ} (hm : m < K1.p) (j : Fin m) :
    atJet (padJet f (m - 4) j.val) S =
      atJet (separant f) S ^ (m - 4) * hasseDeriv j.val S := by
  have hj := j.isLt
  exact atJet_padJet f S hf (m - 4) j.val (by omega) (hj.trans hm)
private theorem reconstruct_actual {f : Row 3} {S : (Polynomial Geom)} (hdeg : S.natDegree < taylorLength)
    (hS : RegularAt 2 f S) :
    reconstruct f (coefficientNumerator taylorLength f) (jetPoint S) = coefficientPoint S := by
  funext i
  rw [reconstruct, graphPoint_of_actual hS, eval_genericRow]
  let s := genericCoeff (atJet (separant f) S)
  have hs : s ≠ 0 := genericCoeff_ne_zero hS.2
  have hp : taylorLength < K1.p := by decide
  unfold coefficientNumerator
  rw [map_sum]
  change (∑ j : Fin taylorLength, MvPolynomial.eval (jetPoint S) _) /
    s ^ (taylorLength - 4) = _
  simp only [map_mul, MvPolynomial.eval_C, eval_genericRow, atJet_padded f S hS.1 hp, map_pow]
  change _ = algebraMap Geom GeometricX (S.coeff i)
  rw [div_eq_iff (pow_ne_zero _ hs), ← taylor_coefficients_aux S taylorLength hdeg i.val,
    Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  change _ * (s ^ (taylorLength - 4) * _) = _ * s ^ (taylorLength - 4)
  rw [mul_comm (s ^ (taylorLength - 4)), ← mul_assoc]
private theorem actual {f : Row 3}
    (hcut : RepresentsOnGraph f (oldCut f) (cut taylorLength f))
    (hnext : RepresentsOnGraph f (oldNext f) (next taylorLength f))
    (S : (Polynomial Geom)) (hdeg : S.natDegree ≤ physicalDegree) (hS : RegularAt 2 f S) :
    atJet (oldCut f) S = 0 ∧ atJet (oldNext f) S = 0 ∧
      reconstruct f (coefficientNumerator taylorLength f) (jetPoint S) = coefficientPoint S := by
  have hlength (d m : ℕ) (hd : d < m) (hm : 4 ≤ m) : d - 3 < m - 3 := by omega
  have hdeg' : S.natDegree < taylorLength := Nat.lt_succ_of_le hdeg
  have hfirst := hlength S.natDegree taylorLength hdeg' (by decide)
  have hsecond : S.natDegree - 3 < taylorLength - 2 :=
    hfirst.trans_le (Nat.sub_le_sub_left (by decide : 2 ≤ 3) _)
  refine ⟨actual_zero_of_represents hS hcut ?_, actual_zero_of_represents hS hnext ?_,
    reconstruct_actual hdeg' hS⟩
  · rw [cut, eval_genericRow, third_atJet_zero hS.1 _ hfirst, map_zero]
  · rw [next, eval_genericRow, third_atJet_zero hS.1 _ hsecond, map_zero]
theorem lifted_chart (n : ℕ) (f : Fin n → Row 3) (hf : SecondFactors top f) (i : Fin n) :
    Nonempty (LiftedChart top (f i)) := by
  have hb := (Finset.single_le_sum (f := fun k => (f k).totalDegree)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)).trans hf.total
  have hj := (Finset.single_le_sum (f := fun k => indexDegree (f k))
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)).trans hf.index
  have ht := (Finset.single_le_sum (f := fun k => (f k).degreeOf 2)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)).trans hf.coordinate
  obtain ⟨hg, he, hn, hc⟩ := support (f i) hb hj ht
  have hrep : RepresentsOnGraph (f i) (oldCut (f i)) (cut taylorLength (f i)) :=
    represents (f i) (taylorLength - 3)
  have hrep' : RepresentsOnGraph (f i) (oldNext (f i)) (next taylorLength (f i)) :=
    represents (f i) (taylorLength - 2)
  exact ⟨{
    cut := cut taylorLength (f i)
    next := next taylorLength (f i)
    numerator := coefficientNumerator taylorLength (f i)
    graph_box := hg
    cut_box := he
    next_box := hn
    coefficient_box := hc
    cut_represents := hrep
    next_represents := hrep'
    actual := actual hrep hrep'
  }⟩
end
end Low6966Leading_1
end
section
namespace Low6966Leading
noncomputable section
variable {top : Fin 16}
open K1_13 (Geom Row atJet jet indexDegree)
open K1_13_5 (RegularAt)
open Low6966Leading (FirstRow)
open K1_13_5_1
open Low6966Prices (LowerRow TrueWeightLE physicalDegree anchorCutoff lowerWidth lowerIndex lowerTop)
open MvPolynomial UniqueFactorizationMonoid
open scoped Polynomial BigOperators
open K1_13_1 (coeff_flatten)
private theorem trueWeight_iff {n D : ℕ} (P : Row n) :
    TrueWeightLE P D ↔
      ((MvPolynomial.optionEquivRight Geom (Fin n)).symm P).weightedTotalDegree
        (fun v => v.elim 1 (fun i => physicalDegree - i.val)) ≤ D := by
  classical
  rw [MvPolynomial.weightedTotalDegree, Finset.sup_le_iff]
  constructor
  · intro h u hu
    have hc : (P.coeff u.some).coeff (u none) ≠ 0 := by
      rw [← coeff_flatten, Finsupp.optionElim_some]
      exact MvPolynomial.mem_support_iff.mp hu
    have hm : u.some ∈ P.support :=
      MvPolynomial.mem_support_iff.mpr (fun hz => hc (by simp [hz]))
    have hi := Polynomial.le_natDegree_of_ne_zero hc
    rw [← Finsupp.optionElim_some u, Finsupp.weight_optionElim, one_mul]
    apply (Nat.add_le_add_right hi _).trans
    simpa only [Finsupp.weight_apply, smul_eq_mul, Nat.mul_comm] using h _ hm
  · intro h m hm
    let d := (P.coeff m).natDegree
    have hc : (P.coeff m).coeff d ≠ 0 :=
      Polynomial.leadingCoeff_ne_zero.mpr (MvPolynomial.mem_support_iff.mp hm)
    have hu : m.optionElim d ∈ ((MvPolynomial.optionEquivRight Geom (Fin n)).symm P).support :=
      MvPolynomial.mem_support_iff.mpr (by rwa [coeff_flatten])
    have hb := h _ hu
    rw [Finsupp.weight_optionElim, one_mul] at hb
    simpa only [Finsupp.weight_apply, smul_eq_mul, Nat.mul_comm] using hb
private theorem increase_budget {a b c C t d : ℕ} (hc : 0 < c) (hC : c ≤ C)
    (ht : a * t ≤ 2 * b) (hd : d + a * c ^ 2 ≤ (2 * c - 1) * b) :
    d + a * c ^ 2 + a * ((C - c) * t) ≤ (2 * C - 1) * b := by
  have hincr := Nat.mul_le_mul_left (C - c) ht
  have he : 2 * C - 1 = (2 * c - 1) + 2 * (C - c) := by omega
  rw [he, Nat.add_mul]
  rw [show a * ((C - c) * t) = (C - c) * (a * t) by ring,
    show 2 * (C - c) * b = (C - c) * (2 * b) by ring]
  exact Nat.add_le_add hd hincr
private theorem aggregate_contracted {ι : Type*} (T : Finset ι) (b c d : ι → ℕ) (B a r : ℕ)
    (hb : ∑ i ∈ T, b i ≤ B) (hc : ∑ i ∈ T, c i ≤ r) (hB : a * r ≤ B)
    (hbase : ∀ i ∈ T, a * c i ≤ b i)
    (hzero : ∀ i ∈ T, c i = 0 → d i ≤ b i)
    (hpos : ∀ i ∈ T, 0 < c i → d i + a * (c i)^2 ≤ (2 * c i - 1) * b i) :
    ∑ i ∈ T, d i ≤ max B ((2 * r - 1) * B - a * r^2) := by
  let C := ∑ i ∈ T, c i
  have hci (i : ι) (hi : i ∈ T) : c i ≤ C := Finset.single_le_sum (fun j _ => Nat.zero_le (c j)) hi
  by_cases hC : C = 0
  · have h := (Finset.sum_le_sum fun i hi => hzero i hi (by have := hci i hi; omega)).trans hb
    exact h.trans (le_max_left _ _)
  have hCpos := Nat.pos_of_ne_zero hC
  have hterm (i : ι) (hi : i ∈ T) : d i + a * (C * c i) ≤ (2 * C - 1) * b i := by
    by_cases hi₀ : c i = 0
    · rw [hi₀, Nat.mul_zero, Nat.mul_zero, Nat.add_zero]
      exact (hzero i hi hi₀).trans (by
        simpa using Nat.mul_le_mul_right (b i) (show 1 ≤ 2 * C - 1 by omega))
    · have h := increase_budget (Nat.pos_of_ne_zero hi₀) (hci i hi)
        ((hbase i hi).trans (by omega : b i ≤ 2 * b i)) (hpos i hi (Nat.pos_of_ne_zero hi₀))
      have he : C = c i + (C - c i) := by have := hci i hi; omega
      have hweight : a * (C * c i) = a * (c i)^2 + a * ((C - c i) * c i) := by
        calc
          _ = a * ((c i + (C - c i)) * c i) := congrArg (fun n => a * (n * c i)) he
          _ = _ := by ring
      rw [hweight, ← Nat.add_assoc]
      exact h
  have hs : (∑ i ∈ T, (d i + a * (C * c i))) ≤ (2 * C - 1) * B :=
    (Finset.sum_le_sum hterm).trans (by
      rw [← Finset.mul_sum]
      exact Nat.mul_le_mul_left _ hb)
  have hjoint : (∑ i ∈ T, d i) + a * C ^ 2 ≤ (2 * C - 1) * B := by
    simp only [Finset.sum_add_distrib, ← Nat.mul_assoc, ← Finset.mul_sum] at hs
    change (∑ i ∈ T, d i) + (a * C) * C ≤ _ at hs
    rwa [Nat.mul_assoc, ← pow_two] at hs
  have ha : a * (r + C) ≤ 2 * B := by
    calc
      _ ≤ a * (r + r) := Nat.mul_le_mul_left _ (Nat.add_le_add_left hc r)
      _ = 2 * (a * r) := by ring
      _ ≤ _ := Nat.mul_le_mul_left 2 hB
  have hfinal := increase_budget hCpos hc ha hjoint
  have he : r = C + (r - C) := by omega
  have hsq : a * C ^ 2 + a * ((r - C) * (r + C)) = a * r ^ 2 := by
    calc
      _ = a * C ^ 2 + a * ((r - C) * ((C + (r - C)) + C)) := by
        exact congrArg (fun n => a * C ^ 2 + a * ((r - C) * (n + C))) he
      _ = a * (C + (r - C)) ^ 2 := by ring
      _ = _ := by rw [← he]
  exact (Nat.le_sub_of_add_le (by simpa only [Nat.add_assoc, hsq] using hfinal)).trans (le_max_right _ _)
theorem factor_cover (g : Row 3) (hg : LowerRow top g) :
    ∃ (n : ℕ) (f : Fin n → Row 3) (q : Row 2), SecondFactors top f ∧ FirstRow top q ∧
      ∀ S : (Polynomial Geom), atJet g S = 0 →
        atJet q S = 0 ∨ ∃ i, RegularAt 2 (f i) S := by
  classical
  obtain ⟨hg₀, hgt₀, hgi₀, hgw⟩ := hg
  let _ : StrongNormalizationMonoid (Row 3) := UniqueFactorizationMonoid.strongNormalizationMonoid
  let A := normalizedFactors g
  let T := A.toFinset
  let c (f : Row 3) := (view f).natDegree
  let P := T.filter fun f => 0 < c f
  let n := Fintype.card ↥P
  let e : Fin n ≃ ↥P := (Fintype.equivFin ↥P).symm
  let f : Fin n → Row 3 := fun i => (e i).val
  let q : Row 2 := ∏ a ∈ T, elimination a
  have hmem (a : Row 3) (ha : a ∈ T) : a ∈ A := Multiset.mem_toFinset.mp ha
  have hirr (a : Row 3) (ha : a ∈ T) : Irreducible a :=
    irreducible_of_normalized_factor a (hmem a ha)
  have hf (i : Fin n) : f i ∈ T ∧ 0 < c (f i) := Finset.mem_filter.mp (e i).property
  have hdvd : (∏ a ∈ T, a) ∣ g :=
    (Multiset.toFinset_prod_dvd_prod A).trans (prod_normalizedFactors hg₀).dvd
  have hsum (w : Fin 3 → ℕ) :
      (∑ a ∈ T, a.weightedTotalDegree w) ≤ g.weightedTotalDegree w :=
    sum_weightedTotalDegree_le_of_prod_dvd w T id hg₀ hdvd
  have htop (a : Row 3) : c a = a.degreeOf 2 := view_degree a
  have hc : ∑ a ∈ T, c a ≤ lowerTop top := by
    have hbound : g.weightedTotalDegree (fun i => i.val) ≤ lowerIndex top :=
      (K1_13_1.indexDegree_eq g) ▸ hgi₀
    have h : 2 * (∑ a ∈ T, c a) ≤ lowerIndex top := calc
      _ = ∑ a ∈ T, (2 * c a) := Finset.mul_sum T c 2
      _ ≤ ∑ a ∈ T, a.weightedTotalDegree (fun i => i.val) := by
        apply Finset.sum_le_sum
        intro a _
        exact (Nat.le_add_left _ _).trans (view_coeff_weight (fun i => i.val) a (c a) le_rfl)
      _ ≤ _ := (hsum _).trans hbound
    unfold lowerTop
    omega
  have hr : lowerTop top < K1.p := by fin_cases top <;> decide
  have he₀ (a : Row 3) (ha : a ∈ T) : elimination a ≠ 0 := by
    have hca := (Finset.single_le_sum (fun i _ => Nat.zero_le (c i)) ha).trans hc
    exact elimination_ne_zero (hirr a ha) (hca.trans_lt hr)
  have hq (w : Fin 3 → ℕ) (B : ℕ) (hb : g.weightedTotalDegree w ≤ B)
      (hB : w 2 * lowerTop top ≤ B) :
      q.weightedTotalDegree (fun i => w i.castSucc) ≤
        max B ((2 * lowerTop top - 1) * B - w 2 * lowerTop top ^ 2) := by
    let v : Fin 2 → ℕ := fun i => w i.castSucc
    rw [show q = ∏ a ∈ T, elimination a from rfl, weightedTotalDegree_prod v T _ he₀]
    apply aggregate_contracted T (fun a => a.weightedTotalDegree w) c
      (fun a => (elimination a).weightedTotalDegree v) B (w 2) (lowerTop top)
      ((hsum w).trans hb) hc hB
    · intro a _
      exact (Nat.le_add_left _ _).trans (view_coeff_weight w a (c a) le_rfl)
    · intro a _ ha
      exact elimination_weight_zero w a ha
    · intro a _ ha
      exact elimination_weight_positive w a ha
  have hqtotal : q.totalDegree ≤ firstWidth top := by
    have hb : g.totalDegree ≤ lowerWidth top := hgt₀
    have h := hq (1 : Fin 3 → ℕ) (lowerWidth top)
      (by simpa only [weightedTotalDegree_one] using hb)
      (by fin_cases top <;> decide)
    have hv : (fun i : Fin 2 => (1 : Fin 3 → ℕ) i.castSucc) = (1 : Fin 2 → ℕ) := by
      funext i
      simp
    rw [hv, weightedTotalDegree_one, Pi.one_apply, one_mul] at h
    exact h
  have hqindex : indexDegree q ≤ firstIndex top := by
    rw [K1_13_1.indexDegree_eq] at hgi₀ ⊢
    have hbudget : (2 : ℕ) * lowerTop top ≤ lowerIndex top := by
      unfold lowerTop
      omega
    exact hq (fun i => i.val) (lowerIndex top) hgi₀ hbudget
  have hsub (d : Row 3 → ℕ) : (∑ i, d (f i)) ≤ ∑ a ∈ T, d a := by
    calc
      _ = ∑ a : ↥P, d a.val := e.sum_comp _
      _ = ∑ a ∈ P, d a := Finset.sum_coe_sort P d
      _ ≤ _ := Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
  refine ⟨n, f, q, ⟨fun i => hirr _ (hf i).1, fun i => htop _ ▸ (hf i).2, ?_, ?_, ?_, ?_⟩,
    ⟨Finset.prod_ne_zero_iff.mpr he₀, hqtotal, hqindex⟩, ?_⟩
  · intro i
    let E := MvPolynomial.optionEquivRight Geom (Fin 3)
    have hdi := map_dvd E.symm (dvd_of_mem_normalizedFactors (hmem _ (hf i).1))
    have hgn : E.symm g ≠ 0 := fun hz => hg₀ (E.symm.injective (hz.trans (map_zero _).symm))
    exact (trueWeight_iff _).mpr
      ((weightedTotalDegree_le_of_dvd _ hdi hgn).trans ((trueWeight_iff _).mp hgw))
  · exact (hsub _).trans ((by simpa only [weightedTotalDegree_one] using hsum (1 : Fin 3 → ℕ) :
      (∑ a ∈ T, a.totalDegree) ≤ g.totalDegree).trans hgt₀)
  · exact (hsub _).trans ((by simpa only [← K1_13_1.indexDegree_eq] using hsum (fun i => i.val) :
      (∑ a ∈ T, indexDegree a) ≤ indexDegree g).trans hgi₀)
  · simpa only [htop] using (hsub c).trans hc
  · intro S hS
    have hz := map_dvd (eval (jet S)) (prod_normalizedFactors hg₀).symm.dvd
    change atJet g S ∣ eval (jet S) A.prod at hz
    rw [hS, zero_dvd_iff, map_multiset_prod, Multiset.prod_eq_zero_iff, Multiset.mem_map] at hz
    obtain ⟨a, ha, hzero⟩ := hz
    have haT : a ∈ T := Multiset.mem_toFinset.mpr ha
    rcases elimination_eval a S hzero with h | ⟨hp, hr⟩
    · left
      change eval (jet S) (∏ a ∈ T, elimination a) = 0
      rw [map_prod]
      exact Finset.prod_eq_zero haT h
    · right
      let j : ↥P := ⟨a, Finset.mem_filter.mpr ⟨haT, hp⟩⟩
      refine ⟨e.symm j, ?_⟩
      change RegularAt 2 ((e (e.symm j)).val) S
      rw [Equiv.apply_symm_apply]
      exact hr
end
end Low6966Leading
end
namespace Low6966LeadingFirst
noncomputable section
variable {top : Fin 16}
open K1_13 MvPolynomial UniqueFactorizationMonoid
open K1_13_5 (RegularAt)
open Low6966Leading (FirstRow FirstFactors firstWidth firstIndex)
open scoped BigOperators Polynomial
private def firstView : Row 2 ≃ₐ[(Polynomial Geom)] (Polynomial (Row 1)) :=
  (renameEquiv (Polynomial Geom) finSuccEquivLast).trans (optionEquivLeft (Polynomial Geom) (Fin 1))
private abbrev valueView : Row 1 ≃ₐ[(Polynomial Geom)] (Polynomial (Polynomial Geom)) :=
  uniqueAlgEquiv (Polynomial Geom) (Fin 1)
private theorem firstView_degree (f : Row 2) : (firstView f).natDegree = f.degreeOf 1 := by
  change (optionEquivLeft _ _ (rename finSuccEquivLast f)).natDegree = f.degreeOf 1
  rw [natDegree_optionEquivLeft]
  exact degreeOf_rename_of_injective finSuccEquivLast.injective (Fin.last 1)
private theorem firstView_pderiv (f : Row 2) :
    firstView (pderiv 1 f) = (firstView f).derivative := by
  change optionEquivLeft _ _ (rename finSuccEquivLast (pderiv 1 f)) =
    (optionEquivLeft _ _ (rename finSuccEquivLast f)).derivative
  rw [← pderiv_rename finSuccEquivLast.injective,
    show finSuccEquivLast (1 : Fin 2) = none from finSuccEquivLast_last,
    optionEquivLeft_pderiv_none]
private theorem valueView_eval (g : Row 1) (S : (Polynomial Geom)) :
    (valueView g).eval S = MvPolynomial.eval (jet S) g := by
  have h := eval₂_uniqueAlgEquiv (f := g) (φ := RingHom.id (Polynomial Geom)) (a := jet S)
  have hzero : jet S (default : Fin 1) = S := by
    change Polynomial.hasseDeriv 0 S = S
    simp
  simpa only [Polynomial.eval₂_id, MvPolynomial.eval₂_id, hzero] using h
private theorem firstView_eval (f : Row 2) (S : (Polynomial Geom)) :
    ((firstView f).map (MvPolynomial.eval (jet S))).eval (jet S (1 : Fin 2)) =
      atJet f S := by
  rw [firstView, AlgEquiv.trans_apply, renameEquiv_apply, ← optionEquivLeft_elim_eval,
    eval_rename, atJet]
  apply congrArg (fun x : Fin 2 → (Polynomial Geom) => MvPolynomial.eval x f)
  funext i
  fin_cases i <;> rfl
private theorem valueView_degree_le (g : Row 1) : (valueView g).natDegree ≤ g.totalDegree := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro k hk
  rw [valueView, coeff_uniqueAlgEquiv]
  by_contra hn
  have h := le_totalDegree (mem_support_iff.mpr hn)
  change (Finsupp.single (default : Fin 1) k).degree ≤ g.totalDegree at h
  rw [Finsupp.degree_single] at h
  exact (not_le_of_gt hk) h
private theorem firstView_coeff_bound (f : Row 2) (k : ℕ) (hk : k ≤ f.totalDegree) :
    k + (valueView ((firstView f).coeff k)).natDegree ≤ f.totalDegree := by
  change k + (valueView ((optionEquivLeft _ _ (rename finSuccEquivLast f)).coeff k)).natDegree ≤ _
  have hdeg : (rename finSuccEquivLast f).totalDegree = f.totalDegree :=
    totalDegree_renameEquiv finSuccEquivLast f
  have hh := totalDegree_coeff_optionEquivLeft_add_le (Polynomial Geom) (Fin 1)
    (rename finSuccEquivLast f) k
    (by rw [hdeg]; exact hk)
  rw [hdeg] at hh
  exact (Nat.add_le_add_left (valueView_degree_le _) _).trans (by simpa [add_comm] using hh)
private def eliminant (f : Row 2) : (Polynomial (Polynomial Geom)) :=
  let A := firstView f
  if 0 < A.natDegree then
    valueView (A.resultant A.derivative A.natDegree (A.natDegree - 1))
  else valueView (A.coeff 0)
set_option maxHeartbeats 600000 in
private theorem eliminant_spec (f : Row 2) (hf : Irreducible f) (hb : f.totalDegree ≤ (firstWidth top)) :
    eliminant f ≠ 0 ∧ (eliminant f).natDegree ≤ f.totalDegree * ((firstWidth top) - 1) ∧
      ∀ S : (Polynomial Geom), atJet f S = 0 → (eliminant f).eval S = 0 ∨
        (0 < f.degreeOf 1 ∧ RegularAt 1 f S) := by
  let A := firstView f
  let c := A.natDegree
  let b := f.totalDegree
  have hcb : c ≤ b := by
    change (firstView f).natDegree ≤ f.totalDegree
    exact (firstView_degree f).le.trans (f.degreeOf_le_totalDegree 1)
  have hAb : A ≠ 0 := (map_ne_zero_iff _ firstView.injective).mpr hf.ne_zero
  by_cases hc : 0 < c
  · let R := A.resultant A.derivative c (c - 1)
    have hform : eliminant f = valueView R := ite_eq_left hc
    have hcast : (c : Row 1) ≠ 0 := by
      have : CharP Geom K1.p := charP_of_injective_ringHom embed.injective K1.p
      have : CharP (Polynomial Geom) K1.p :=
        charP_of_injective_ringHom (Polynomial.C_injective (R := Geom)) K1.p
      have : CharP (Row 1) K1.p :=
        charP_of_injective_ringHom (MvPolynomial.C_injective (σ := Fin 1) (R := (Polynomial Geom))) K1.p
      intro h
      have hp : K1.p ∣ c := (CharP.cast_eq_zero_iff (Row 1) K1.p c).mp h
      exact (not_le_of_gt (hcb.trans_lt (hb.trans_lt (by fin_cases top <;> decide : (firstWidth top) < K1.p))))
        (Nat.le_of_dvd hc hp)
    have hder : A.derivative ≠ 0 := by
      intro h
      have hz := congrArg (fun P : (Polynomial (Row 1)) => P.coeff (c - 1)) h
      rw [Polynomial.coeff_derivative, Nat.sub_add_cancel hc, Polynomial.coeff_zero] at hz
      have hnat : (((c - 1 : ℕ) : Row 1) + 1) = (c : Row 1) := calc
        _ = ((c - 1 + 1 : ℕ) : Row 1) := by rw [Nat.cast_add, Nat.cast_one]
        _ = _ := congrArg (fun k : ℕ => (k : Row 1)) (Nat.sub_add_cancel hc)
      rw [hnat] at hz
      change A.leadingCoeff * (c : Row 1) = 0 at hz
      exact (mul_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr hAb) hcast) hz
    have hR : R ≠ 0 :=
      Polynomial.resultant_derivative_ne_zero_of_irreducible A (hf.map firstView) hder
    have hdeg : (valueView R).natDegree + c ^ 2 ≤ (2 * c - 1) * b := by
      let B := A.map valueView.toRingHom
      have h := Polynomial.natDegree_resultant_derivative_padded_add_sq_le B c b (by
        intro k hk
        rw [Polynomial.coeff_map]
        exact firstView_coeff_bound f k (hk.trans hcb))
      dsimp only [B] at h
      rw [Polynomial.derivative_map, Polynomial.resultant_map_map] at h
      exact h
    have hbudget : (valueView R).natDegree ≤ b * (b - 1) := by
      have hbpos : 1 ≤ b := hc.trans_le hcb
      have hcpos : 1 ≤ 2 * c := by omega
      zify [hbpos, hcpos] at hdeg ⊢
      nlinarith [sq_nonneg ((b : ℤ) - (c : ℤ))]
    refine ⟨by rw [hform]; exact (map_ne_zero_iff _ valueView.injective).mpr hR, ?_, ?_⟩
    · rw [hform]
      exact hbudget.trans (Nat.mul_le_mul_left b (Nat.sub_le_sub_right hb 1))
    · intro S hS
      by_cases hS' : atJet (pderiv 1 f) S = 0
      · left
        rw [hform, valueView_eval]
        exact Polynomial.map_resultant_eq_zero_of_common_root (MvPolynomial.eval (jet S))
          A A.derivative le_rfl (Polynomial.natDegree_derivative_le A) (Or.inl hc.ne')
          (jet S (1 : Fin 2)) ((firstView_eval f S).trans hS) (by
            rw [show A.derivative = firstView (pderiv 1 f) from (firstView_pderiv f).symm]
            exact (firstView_eval _ S).trans hS')
      · exact Or.inr ⟨(firstView_degree f) ▸ hc, hS, hS'⟩
  · have hform : eliminant f = valueView (A.coeff 0) := ite_eq_right hc
    have hAc : A = Polynomial.C (A.coeff 0) :=
      Polynomial.eq_C_of_natDegree_le_zero (Nat.eq_zero_of_not_pos hc).le
    have hA0 : A.coeff 0 ≠ 0 := fun h => hAb (by simpa [h] using hAc)
    refine ⟨by rw [hform]; exact (map_ne_zero_iff _ valueView.injective).mpr hA0, ?_, ?_⟩
    · rw [hform]
      have h := firstView_coeff_bound f 0 (Nat.zero_le _)
      exact (by simpa using h : (valueView (A.coeff 0)).natDegree ≤ b).trans
        (by simpa using Nat.mul_le_mul_left b (by fin_cases top <;> decide : 1 ≤ (firstWidth top) - 1))
    · intro S hS
      left
      have h := (firstView_eval f S).trans hS
      change (A.map _).eval _ = 0 at h
      conv at h => lhs; rw [hAc]
      rw [hform, valueView_eval]
      simpa only [Polynomial.map_C, Polynomial.eval_C] using h
theorem proof (q : Row 2) (hq : FirstRow top q) :
    ∃ (n : ℕ) (f : Fin n → Row 2) (u : (Polynomial (Polynomial Geom))), FirstFactors top f ∧ u ≠ 0 ∧
      u.natDegree ≤ (firstWidth top) * ((firstWidth top) - 1) ∧
      ∀ S : (Polynomial Geom), atJet q S = 0 →
        u.eval S = 0 ∨ ∃ i, RegularAt 1 (f i) S := by
  classical
  let _ : StrongNormalizationMonoid (Row 2) :=
    UniqueFactorizationMonoid.strongNormalizationMonoid
  let M := normalizedFactors q
  let A := M.toFinset
  let T := A.filter fun g => 0 < g.degreeOf 1
  let n := Fintype.card ↥T
  let e : Fin n ≃ ↥T := (Fintype.equivFin ↥T).symm
  let f : Fin n → Row 2 := fun i => (e i).val
  have hA : ∀ g ∈ A, Irreducible g := fun g hg =>
    irreducible_of_normalized_factor g (Multiset.mem_toFinset.mp hg)
  have hdiv : (∏ g ∈ A, g) ∣ q :=
    (Multiset.toFinset_prod_dvd_prod M).trans (prod_normalizedFactors hq.ne_zero).dvd
  have hcap : (∑ g ∈ A, g.totalDegree) ≤ (firstWidth top) := by
    have h := sum_weightedTotalDegree_le_of_prod_dvd (1 : Fin 2 → ℕ) A id hq.ne_zero hdiv
    simp only [id_eq, weightedTotalDegree_one] at h
    exact h.trans hq.total
  have hfactor : ∀ i, f i ∈ A ∧ 0 < (f i).degreeOf 1 := fun i =>
    Finset.mem_filter.mp (e i).property
  have hfdiv : (∏ i, f i) ∣ q := by
    rw [show (∏ i, f i) = ∏ g : ↥T, id g.val from e.prod_comp Subtype.val,
      Finset.prod_coe_sort T id]
    exact (Finset.prod_dvd_prod_of_subset T A id (Finset.filter_subset _ _)).trans hdiv
  have hf : FirstFactors top f := by
    refine ⟨fun i => hA _ (hfactor i).1, fun i => (hfactor i).2, ?_, ?_⟩
    · have h := sum_weightedTotalDegree_le_of_prod_dvd (1 : Fin 2 → ℕ) Finset.univ f hq.ne_zero hfdiv
      simp only [weightedTotalDegree_one] at h
      exact h.trans hq.total
    · have h := sum_weightedTotalDegree_le_of_prod_dvd (fun i : Fin 2 => i.val)
        Finset.univ f hq.ne_zero hfdiv
      simp only [← K1_13_1.indexDegree_eq] at h
      exact h.trans hq.index
  have hspec (g : Row 2) (hg : g ∈ A) :=
    eliminant_spec g (hA g hg) ((Finset.single_le_sum (fun x _ => Nat.zero_le x.totalDegree) hg).trans hcap)
  let u := ∏ g ∈ A, eliminant g
  refine ⟨n, f, u, hf, Finset.prod_ne_zero_iff.mpr (fun g hg => (hspec g hg).1), ?_, ?_⟩
  · calc
      u.natDegree ≤ ∑ g ∈ A, (eliminant g).natDegree := Polynomial.natDegree_prod_le _ _
      _ ≤ ∑ g ∈ A, g.totalDegree * ((firstWidth top) - 1) := Finset.sum_le_sum fun g hg => (hspec g hg).2.1
      _ ≤ (firstWidth top) * ((firstWidth top) - 1) := by rw [← Finset.sum_mul]; exact Nat.mul_le_mul_right _ hcap
  · intro S hS
    have hroot : MvPolynomial.eval (jet S) M.prod = 0 := by
      have hd := map_dvd (MvPolynomial.eval (jet S)) (prod_normalizedFactors hq.ne_zero).symm.dvd
      change atJet q S ∣ _ at hd
      rwa [hS, zero_dvd_iff] at hd
    rw [map_multiset_prod, Multiset.prod_eq_zero_iff, Multiset.mem_map] at hroot
    obtain ⟨g, hgM, hgS⟩ := hroot
    have hgA : g ∈ A := Multiset.mem_toFinset.mpr hgM
    rcases (hspec g hgA).2.2 S hgS with hzero | ⟨hpos, hreg⟩
    · left
      change Polynomial.evalRingHom S u = 0
      rw [show u = ∏ g ∈ A, eliminant g from rfl, map_prod]
      exact Finset.prod_eq_zero_iff.mpr ⟨g, hgA, hzero⟩
    · right
      let j := e.symm ⟨g, Finset.mem_filter.mpr ⟨hgA, hpos⟩⟩
      have hj : f j = g := congrArg Subtype.val (e.apply_symm_apply _)
      exact ⟨j, hj ▸ hreg⟩
end
end Low6966LeadingFirst

section
namespace Low6966Leading
noncomputable section
variable {top : Fin 16}
open P3 (I K node p)
open Low6966Prices (Messages taylorLength)
open K1_13 (Row Geom embed extend indexDegree atJet)
open K1_13_5 (RegularAt NodeCapacity NodeFamily)
open Low6966Leading (FirstFactors)
open K1_13_5_3 (CenterField toCenter constants center chart plane marked toCenter_inj
  marked_injective aeval_plane plane_ne_zero plane_prime chart_degree chart_top
  degreeOf_le_index mem_capped capped_cut_card)
open Polynomial PolynomialDifferential
open scoped BigOperators
open K1_13_5_3 (eval_at_center specialization_flatten)
open K1_13_5_3 (flatten)
private theorem exponent_sufficient : TaylorExponentSufficient 1 taylorLength firstExponent := by
  exact taylorExponentSufficient_firstOrder_tight 133387
private theorem chart_cut_agreement {f : Row 2} {S : (Polynomial Geom)} (hS : RegularAt 1 f S)
    (hD : S.natDegree ≤ 133387) (x y : Geom) :
    MvPolynomial.aeval (marked S)
      (taylorAgreementEquation center (chart f) taylorLength firstExponent (constants x) (constants y))
      = 0 ↔ S.eval x = y := by
  have hsol : differentialSpecialization (chart f) (S.map constants) = 0 := by
    rw [chart, ← map_differentialSpecialization, specialization_flatten, hS.1, Polynomial.map_zero]
  have hsf : differentialSpecialization (PolynomialDifferential.separant (flatten f) 1) S ≠ 0 := by
    change differentialSpecialization
      (MvPolynomial.pderiv (some 1) ((MvPolynomial.optionEquivRight Geom (Fin 2)).symm f)) S ≠ 0
    rw [← MvPolynomial.optionEquivRight_symm_pderiv]
    exact (specialization_flatten (MvPolynomial.pderiv 1 f) S).substr hS.2
  have hsep : jetEvaluation (PolynomialDifferential.separant (chart f) (Fin.last 1))
      center (marked S) ≠ 0 := by
    change jetEvaluation (PolynomialDifferential.separant (chart f) 1) center (marked S) ≠ 0
    rw [marked, ← eval_differentialSpecialization, chart, ← map_separant,
      ← map_differentialSpecialization, eval_at_center]
    exact fun he => hsf (toCenter_inj (he.trans (map_zero _).symm))
  have hdeg : (S.map constants).degree < (taylorLength : WithBot ℕ) := by
    have hb : (S.map constants).natDegree ≤ 133387 := Polynomial.natDegree_map_le.trans hD
    exact Polynomial.degree_le_natDegree.trans_lt (by exact_mod_cast Nat.lt_succ_of_le hb)
  have hcharG : CharP Geom P3.p := charP_of_injective_ringHom embed.injective P3.p
  have : CharP CenterField P3.p := charP_of_injective_ringHom constants.injective P3.p
  have hpiv : ∀ i : ℕ, 1 < i → i < taylorLength → (i.choose 1 : CenterField) ≠ 0 := by
    intro i hi ht
    rw [Nat.choose_one_right]
    intro hz
    have hp := Nat.le_of_dvd (by omega : 0 < i)
      ((CharP.cast_eq_zero_iff CenterField P3.p i).mp hz)
    change 0x7f000001 ≤ i at hp
    change i < 133388 at ht
    omega
  rw [taylorAgreementEquation_eq_zero_iff center (chart f) exponent_sufficient (marked S)
      (by rwa [aeval_initialJetSeparant]) (constants x) (constants y)]
  rw [marked, rationalTaylorPolynomial_polynomialJet center (chart f) (S.map constants)
    hsol hsep hdeg hpiv, Polynomial.eval_map_apply, constants.injective.eq_iff]
private theorem plane_capped (f : Row 2) :
    plane f ∈ MvPolynomial.restrictCappedDegree (Fin 2) CenterField 1
      f.totalDegree (indexDegree f) := by
  intro m hm
  have hf := MvPolynomial.support_map_subset toCenter f hm
  exact ⟨MvPolynomial.le_totalDegree hf,
    (MvPolynomial.monomial_le_degreeOf 1 hf).trans (degreeOf_le_index f)⟩
private def nodeCut (w : I → K) (f : Row 2) (i : I) : MvPolynomial (Fin 2) CenterField :=
  taylorAgreementEquation center (chart f) taylorLength firstExponent
    (constants (embed (node i))) (constants (embed (w i)))
private theorem nodeCut_capped (w : I → K) (f : Row 2)
    (hB : f.totalDegree ≤ (firstWidth top)) (hJ : indexDegree f ≤ (firstIndex top)) (i : I) :
    nodeCut w f i ∈ MvPolynomial.restrictCappedDegree (Fin 2) CenterField 1
      (firstChartTotal top) (firstChartTop top) := by
  have ht : (nodeCut w f i).totalDegree ≤ (firstChartTotal top) := by
    refine (totalDegree_taylorAgreementEquation_le center (chart f)
      exponent_sufficient _ _).trans ?_
    exact Nat.add_le_add_left (Nat.mul_le_mul_left firstExponent
      (Nat.sub_le_sub_right ((chart_degree f).trans hB) 1)) 1
  refine mem_capped _ ht (le_min ((MvPolynomial.degreeOf_le_totalDegree _ _).trans ht) ?_)
  exact degreeOf_taylorAgreementEquation_firstOrder_le center (chart f) (firstIndex top)
    taylorLength firstExponent exponent_sufficient
    ((chart_top f).trans ((degreeOf_le_index f).trans hJ)) _ _
private theorem nodeCut_vanishes {w : I → K} {f : Row 2} {S : (Polynomial K)}
    (hreg : RegularAt 1 f (extend S)) (hD : S.natDegree ≤ 133387) (i : I) :
    MvPolynomial.aeval (marked (extend S)) (nodeCut w f i) = 0 ↔
      S.eval (node i) = w i := by
  rw [nodeCut, chart_cut_agreement hreg (Polynomial.natDegree_map_le.trans hD),
    Polynomial.eval_map_apply, embed.injective.eq_iff]
private theorem factor_capacity {w Γ s} (h : Messages w Γ s) (f : Row 2)
    (hf : Irreducible f) (hp : 0 < f.degreeOf 1)
    (hB : f.totalDegree ≤ (firstWidth top)) (hJ : indexDegree f ≤ (firstIndex top))
    (hreg : ∀ γ ∈ Γ, RegularAt 1 f (extend (s γ))) :
    NodeCapacity w Γ s
      (MvPolynomial.cappedDegreeMixedVolume f.totalDegree (indexDegree f) (firstChartTotal top) (firstChartTop top)) := by
  classical
  let P := Ideal.span {plane f}
  let x (γ : K) := marked (extend (s γ))
  have hx : Set.InjOn x (Γ : Set K) := by
    intro γ hγ η hη heq
    exact h.distinct hγ hη (Polynomial.map_injective embed embed.injective (marked_injective heq))
  have hxg : ∀ γ ∈ Γ, MvPolynomial.aeval (x γ) (plane f) = 0 := by
    intro γ hγ
    change MvPolynomial.aeval (marked (extend (s γ))) (plane f) = 0
    rw [aeval_plane, (hreg γ hγ).1, map_zero]
  have hxe (γ : K) (hγ : γ ∈ Γ) (i : I) :
      MvPolynomial.aeval (x γ) (nodeCut w f i) = 0 ↔ (s γ).eval (node i) = w i :=
    nodeCut_vanishes (hreg γ hγ) (h.degree γ hγ) i
  refine ⟨Finset.univ.filter (fun i => nodeCut w f i ∈ P), ?_, ?_⟩
  · intro i hi γ hγ
    apply (hxe γ hγ i).mp
    obtain ⟨q, hq⟩ := Ideal.mem_span_singleton.mp (Finset.mem_filter.mp hi).2
    rw [hq, map_mul, hxg γ hγ, zero_mul]
  · intro i hi
    have hi' : nodeCut w f i ∉ P := by
      intro hh
      exact hi (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hh⟩)
    let hits := Γ.filter fun γ => (s γ).eval (node i) = w i
    have hh : (hits.image x).card ≤ _ := capped_cut_card (by fin_cases top <;> decide : 0 < (firstChartTotal top))
      (by fin_cases top <;> decide : 0 < (firstChartTop top)) (plane_ne_zero hf.ne_zero) (plane_prime hf hp)
      (plane_capped f) (nodeCut_capped w f hB hJ i) hi' (hits.image x) (by
        intro z hz
        obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp hz
        obtain ⟨hm, hh⟩ := Finset.mem_filter.mp hγ
        exact ⟨hxg γ hm, (hxe γ hm i).mpr hh⟩)
    rwa [Finset.card_image_of_injOn (hx.mono (Finset.filter_subset _ _))] at hh
theorem first_order_cover {w Γ s} (h : Messages w Γ s)
    {n : ℕ} (f : Fin n → Row 2) (hf : FirstFactors top f)
    (hregular : ∀ γ ∈ Γ, ∃ i, RegularAt 1 (f i) (extend (s γ))) :
    ∃ C : NodeFamily w Γ s, Γ ⊆ C.labels ∧ C.n ≤ (firstWidth top) ∧
      C.totalCap ≤ (firstMixedBudget top) := by
  classical
  let part (i : Fin n) := Γ.filter fun γ => RegularAt 1 (f i) (extend (s γ))
  let cap (i : Fin n) :=
    MvPolynomial.cappedDegreeMixedVolume (f i).totalDegree (indexDegree (f i)) (firstChartTotal top) (firstChartTop top)
  have hsub : ∀ i, part i ⊆ Γ := fun _ => Finset.filter_subset _ _
  have hlocal : ∀ i, NodeCapacity w (part i) s (cap i) := by
    intro i
    apply factor_capacity (h.mono (hsub i)) (f i) (hf.irreducible i) (hf.positive i)
    · exact (Finset.single_le_sum (fun j _ => Nat.zero_le (f j).totalDegree)
        (Finset.mem_univ i)).trans hf.total
    · exact (Finset.single_le_sum (fun j _ => Nat.zero_le (indexDegree (f j)))
        (Finset.mem_univ i)).trans hf.index
    · exact fun γ hγ => (Finset.mem_filter.mp hγ).2
  let C : NodeFamily w Γ s := ⟨n, part, cap, hsub, hlocal⟩
  refine ⟨C, ?_, ?_, ?_⟩
  · intro γ hγ
    obtain ⟨i, hi⟩ := hregular γ hγ
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, Finset.mem_filter.mpr ⟨hγ, hi⟩⟩
  · change n ≤ (firstWidth top)
    calc
      n = ∑ _ : Fin n, 1 := by simp
      _ ≤ ∑ i, (f i).totalDegree := Finset.sum_le_sum fun i _ =>
        (Nat.succ_le_of_lt (hf.positive i)).trans (MvPolynomial.degreeOf_le_totalDegree _ _)
      _ ≤ (firstWidth top) := hf.total
  · change (∑ i, cap i) ≤ (firstMixedBudget top)
    simp only [cap, MvPolynomial.cappedDegreeMixedVolume, Finset.sum_add_distrib,
      ← Finset.sum_mul]
    exact Nat.add_le_add (Nat.mul_le_mul_right (firstChartTop top) hf.total)
      (Nat.mul_le_mul_right ((firstChartTotal top) - (firstChartTop top)) hf.index)
end
end Low6966Leading
end
section
namespace Low6966Leading
noncomputable section
variable {top : Fin 16}
open P3 (K)
open Low6966Prices (Messages taylorLength lowerCap)
open K1_13 (Row Geom embed extend atJet)
open K1_13_5 (RegularAt NodeFamily mixed3)
open Low6966Leading (lowBox graphBox liftedBox FirstRow)
open Polynomial
open scoped BigOperators
def c1 (top : Fin 16) : Prop :=
  ∀ w Γ s, Messages w Γ s → ∀ n (f : Fin n → Row 3), SecondFactors top f →
    (∀ γ ∈ Γ, ∃ i, RegularAt 2 (f i) (extend (s γ)) ∧ ¬ Whole (f i)) →
    Nonempty (ProperCover top w Γ s)
def c2 (top : Fin 16) : Prop :=
  ∀ w Γ s, Messages w Γ s → ∀ n (f : Fin n → Row 3), SecondFactors top f →
    (∀ γ ∈ Γ, ∃ i, RegularAt 2 (f i) (extend (s γ)) ∧ Whole (f i)) →
    ∃ C : NodeFamily w Γ s, Γ ⊆ C.labels ∧ C.n ≤ Low6966Prices.lowerWidth top ∧ C.totalCap ≤ 133387 * Low6966Prices.lowerWidth top
private theorem roots_card_le {w Γ s} (h : Messages w Γ s) (u : (Polynomial (Polynomial Geom))) (hu : u ≠ 0)
    (hr : ∀ γ ∈ Γ, u.eval (extend (s γ)) = 0) :
    Γ.card ≤ u.natDegree := by
  classical
  let a : K → (Polynomial Geom) := fun γ => extend (s γ)
  have hinj : Set.InjOn a (Γ : Set K) :=
    fun _ hx _ hy heq => h.distinct hx hy (Polynomial.map_injective embed embed.injective heq)
  have hb : (Γ.image a).card ≤ u.natDegree := by
    apply Polynomial.card_le_degree_of_subset_roots
    intro b hb
    change b ∈ Γ.image a at hb
    obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp hb
    exact (Polynomial.mem_roots hu).mpr (hr γ hγ)
  rw [Finset.card_image_of_injOn hinj] at hb
  exact hb
private theorem first_count {w Γ s} (h : Messages w Γ s)
    (q : Row 2) (hq : FirstRow top q) (hr : ∀ γ ∈ Γ, atJet q (extend (s γ)) = 0) :
    46372 * Γ.card ≤ 82385 * (firstMixedBudget top) + 46372 * ((firstWidth top) * (firstWidth top)) := by
  classical
  obtain ⟨n, f, u, hf, hu, hd, hc⟩ := Low6966LeadingFirst.proof q hq
  let ordinary := Γ.filter fun γ => u.eval (extend (s γ)) = 0
  let regular := Γ.filter fun γ => ∃ i, RegularAt 1 (f i) (extend (s γ))
  have hr₀ : ordinary.card ≤ (firstWidth top) * ((firstWidth top) - 1) :=
    (roots_card_le (h.mono (Finset.filter_subset _ _)) u hu
      (fun _ hγ => (Finset.mem_filter.mp hγ).2)).trans hd
  obtain ⟨C, hC, hn, hcap⟩ := first_order_cover (h.mono (Δ := regular) (Finset.filter_subset _ _)) f hf
    (fun _ hγ => (Finset.mem_filter.mp hγ).2)
  have hr₁ := nodeFamily_count C (h.mono (Finset.filter_subset _ _))
  have hr₁' : 46372 * regular.card ≤ 82385 * C.totalCap + 46372 * C.n :=
    (Nat.mul_le_mul_left _ (Finset.card_le_card hC)).trans hr₁
  have covers : Γ ⊆ ordinary ∪ regular := by
    intro γ hγ
    rcases hc _ (hr γ hγ) with ho | hreg
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hγ, ho⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hγ, hreg⟩)
  have htotal := (Finset.card_le_card covers).trans (Finset.card_union_le _ _)
  have hw : 1 ≤ firstWidth top := by fin_cases top <;> decide
  have hs : firstWidth top * (firstWidth top - 1) + firstWidth top =
      firstWidth top * firstWidth top := by
    calc
      _ = firstWidth top * (firstWidth top - 1) + firstWidth top * 1 := by rw [Nat.mul_one]
      _ = _ := by rw [← Nat.mul_add, Nat.sub_add_cancel hw]
  omega
private theorem proper_count {w Γ s} (C : ProperCover top w Γ s) (h : Messages w Γ s) :
    46372 * Γ.card ≤ 46372 * mixedBudget top + (82385 + 2 * 46372) * (invariantBudget top) := by
  classical
  have hm := nodeFamily_count C.multiple h
  have hi := nodeFamily_count C.invariant h
  have hc := (Finset.card_le_card C.cover).trans
    ((Finset.card_union_le _ _).trans
      (Nat.add_le_add_right (Finset.card_union_le _ _) _))
  have hmix := C.mixed
  have hf := C.fresh
  have hn := C.components
  omega
theorem of_children (h1 : c1 top) (h2 : c2 top) : Low6966Prices.c5 top := by
  classical
  intro w Γ s h g hg hr
  obtain ⟨n, f, q, hf, hq, hc⟩ := factor_cover g hg
  let first := Γ.filter fun γ => atJet q (extend (s γ)) = 0
  let proper := Γ.filter fun γ => ∃ i, RegularAt 2 (f i) (extend (s γ)) ∧ ¬ Whole (f i)
  let whole := Γ.filter fun γ => ∃ i, RegularAt 2 (f i) (extend (s γ)) ∧ Whole (f i)
  have hfirst := first_count (h.mono (Δ := first) (Finset.filter_subset _ _)) q hq
    (fun _ hγ => (Finset.mem_filter.mp hγ).2)
  have hpmsg := h.mono (Δ := proper) (Finset.filter_subset _ _)
  obtain ⟨P⟩ := h1 w proper s hpmsg n f hf (fun _ hγ => (Finset.mem_filter.mp hγ).2)
  have hproper := proper_count P hpmsg
  have hwmsg := h.mono (Δ := whole) (Finset.filter_subset _ _)
  obtain ⟨W, hW, hn, hcap⟩ := h2 w whole s hwmsg n f hf (fun _ hγ => (Finset.mem_filter.mp hγ).2)
  have hwhole : 46372 * whole.card ≤ 82385 * W.totalCap + 46372 * W.n :=
    (Nat.mul_le_mul_left _ (Finset.card_le_card hW)).trans (nodeFamily_count W hwmsg)
  have covers : Γ ⊆ first ∪ proper ∪ whole := by
    intro γ hγ
    rcases hc _ (hr γ hγ) with hlow | ⟨i, hreg⟩
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hγ, hlow⟩))
    by_cases hw : Whole (f i)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hγ, i, hreg, hw⟩)
    · exact Finset.mem_union_left _ (Finset.mem_union_right _
        (Finset.mem_filter.mpr ⟨hγ, i, hreg, hw⟩))
  have htotal := (Finset.card_le_card covers).trans
    ((Finset.card_union_le _ _).trans
      (Nat.add_le_add_right (Finset.card_union_le _ _) _))
  have hnumeric : 82385 * (firstMixedBudget top) + 46372 * ((firstWidth top) * (firstWidth top)) +
      (46372 * mixedBudget top + (82385 + 2 * 46372) * (invariantBudget top)) +
      (82385 * (133387 * Low6966Prices.lowerWidth top) + 46372 * Low6966Prices.lowerWidth top) ≤ 46372 * lowerCap top := by
    fin_cases top <;> decide
  omega
end
end Low6966Leading
end

end Merged6967_Low6966LeadingBase

section Merged6967_Low6966RetainedWitness
set_option Elab.async false




set_option Elab.async false
set_option autoImplicit false
set_option Elab.async false
namespace Low6966RetainedCut
noncomputable section
open KoalaRetainedCut (orderAt_off_quotient)
open MvPolynomial
open K1_13 (Row Geom Shape shape InBox OrderAt atJet extend embed indexDegree)
open Low6966Prices (primaryBox primaryCutoff TrueWeightLE ActiveFits physicalDegree)
open P0_9_3_2 (translateTop topHasse topHasse_zero topHasse_coeff source_support sum_add_top total_add_top apply_add_top erase_top_add topHasse_order exact_hasse_not_dvd)
open scoped Polynomial BigOperators
def residualBox (h : Shape) (l : ℕ) : Shape :=
  ⟨primaryBox.b-l*h.b, primaryBox.j-l*h.j, primaryBox.t-l*h.t⟩
private theorem wdegree_pow (w : Fin 4 → ℕ) {H : Row 4} (hn : H ≠ 0) (k : ℕ) :
    (H^k).weightedTotalDegree w = k*H.weightedTotalDegree w := by
  induction k with
  | zero => rw [pow_zero,zero_mul,← MvPolynomial.C_1,weightedTotalDegree_C]
  | succ k ih => rw [pow_succ,weightedTotalDegree_mul _ _ _ (pow_ne_zero k hn) hn,ih,Nat.succ_mul]
theorem residual_box {H G : Row 4} {v l : ℕ} (hv : l ≤ v)
    (hH : H ≠ 0) (hG : G ≠ 0) (hb : InBox (shape (H^v*G)) primaryBox) :
    InBox (shape G) (residualBox (shape H) l) := by
  have bound (w : Fin 4 → ℕ) {cap : ℕ} (hc : (H^v*G).weightedTotalDegree w ≤ cap) :
      G.weightedTotalDegree w ≤ cap - l*H.weightedTotalDegree w := by
    rw [weightedTotalDegree_mul _ _ _ (pow_ne_zero v hH) hG,wdegree_pow _ hH] at hc
    have hs := Nat.mul_le_mul_right (H.weightedTotalDegree w) hv
    omega
  have hb₁ : (H^v*G).totalDegree ≤ primaryBox.b := hb.1
  have hb₂ : indexDegree (H^v*G) ≤ primaryBox.j := hb.2.1
  have hb₃ : (H^v*G).degreeOf 3 ≤ primaryBox.t := hb.2.2
  rw [← weightedTotalDegree_one] at hb₁
  rw [K1_13_1.indexDegree_eq] at hb₂
  rw [← weightedTotalDegree_piSingle] at hb₃
  refine ⟨?_, ?_, ?_⟩
  · change G.totalDegree ≤ primaryBox.b-l*H.totalDegree
    simpa only [weightedTotalDegree_one] using bound (1 : Fin 4 → ℕ) hb₁
  · change indexDegree G ≤ primaryBox.j-l*indexDegree H
    simpa only [← K1_13_1.indexDegree_eq] using bound Fin.val hb₂
  · change G.degreeOf 3 ≤ primaryBox.t-l*H.degreeOf 3
    simpa only [weightedTotalDegree_piSingle] using bound (Pi.single (3 : Fin 4) 1) hb₃
private theorem weight_of_factor {P G : Row 4} {D : ℕ} (hP : P ≠ 0) (hG : G ∣ P)
    (hw : TrueWeightLE P D) : TrueWeightLE G D := by
  let e := MvPolynomial.optionEquivRight Geom (Fin 4)
  have hd := map_dvd e.symm.toRingHom hG
  have hn : e.symm P ≠ 0 := fun h => hP (e.symm.injective (h.trans (map_zero _).symm))
  exact (LowProfile6966.trueWeight_iff G).mpr <|
    (weightedTotalDegree_le_of_dvd _ hd hn).trans ((LowProfile6966.trueWeight_iff P).mp hw)
private theorem topHasse_bounds (box : Shape) (T a : ℕ) (P : Row 4)
    (hb : InBox (shape P) box) (hw : TrueWeightLE P T) :
    InBox (shape (topHasse a P)) box ∧ TrueWeightLE (topHasse a P) T := by
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · change (topHasse a P).totalDegree ≤ box.b
    apply Finset.sup_le
    intro m hm
    have hp := (MvPolynomial.le_totalDegree (source_support hm)).trans hb.1
    rw [total_add_top] at hp
    exact (Nat.le_add_right _ _).trans hp
  · change indexDegree (topHasse a P) ≤ box.j
    apply Finset.sup_le
    intro m hm
    have hp := (Finset.le_sup (f := fun u : Fin 4 →₀ ℕ => u.sum (fun i k => i.val * k))
      (source_support hm)).trans hb.2.1
    rw [sum_add_top Fin.val] at hp
    exact (Nat.le_add_right _ _).trans hp
  · change (topHasse a P).degreeOf 3 ≤ box.t
    apply MvPolynomial.degreeOf_le_iff.mpr
    intro m hm
    have hp := (MvPolynomial.le_degreeOf_of_mem_support 3 (source_support hm)).trans hb.2.2
    rw [apply_add_top] at hp
    exact (Nat.le_add_right _ _).trans hp
  · intro m hm
    have hp := hw _ (source_support hm)
    rw [sum_add_top (fun i => physicalDegree - i.val)] at hp
    rw [topHasse_coeff]
    have hc := Polynomial.natDegree_mul_le
      (p := (↑((m 3 + a).choose a) : (Polynomial Geom))) (q := P.coeff (m + Finsupp.single 3 a))
    rw [Polynomial.natDegree_natCast, zero_add] at hc
    exact (Nat.add_le_add_right hc _).trans ((Nat.add_le_add_left (Nat.le_add_right _ _) _).trans hp)
private theorem topHasse_one_not_dvd (f : Row 4) (hf : Irreducible f)
    (hpos : 0 < f.degreeOf 3) (hsmall : f.degreeOf 3 < K1.p) : ¬ f ∣ topHasse 1 f := by
  classical
  have hdeg : (topHasse 1 f).degreeOf 3 ≤ f.degreeOf 3 - 1 := by
    apply MvPolynomial.degreeOf_le_iff.mpr
    intro m hm
    have h := MvPolynomial.le_degreeOf_of_mem_support 3 (source_support hm)
    rw [apply_add_top] at h
    omega
  have hnz : topHasse 1 f ≠ 0 := by
    have hsup : 0 < f.support.sup (fun m => m (3 : Fin 4)) := by
      rwa [← MvPolynomial.degreeOf_eq_sup]
    obtain ⟨u, hu, htop⟩ := (Finset.le_sup_iff hsup).mp (le_refl _)
    rw [← MvPolynomial.degreeOf_eq_sup] at htop
    have hupos : 0 < u 3 := hpos.trans_le htop
    have hult : u 3 < K1.p := (MvPolynomial.le_degreeOf_of_mem_support 3 hu).trans_lt hsmall
    let m := u.erase 3 + Finsupp.single 3 (u 3 - 1)
    have hsum : m + Finsupp.single 3 1 = u := by
      dsimp [m]
      rw [add_assoc, ← Finsupp.single_add, Nat.sub_add_cancel hupos, erase_top_add]
    have hm : m 3 + 1 = u 3 := by
      rw [← apply_add_top, hsum]
    have hc : (↑(u 3) : (Polynomial Geom)) ≠ 0 := by
      have : CharP Geom K1.p :=
        charP_of_injective_ringHom (RingHom.injective embed) K1.p
      intro hz
      have hz' : (↑(u 3) : Geom) = 0 := by
        simpa only [map_natCast, map_zero] using congrArg (Polynomial.evalRingHom (0 : Geom)) hz
      exact (not_le_of_gt hult)
        (Nat.le_of_dvd hupos ((CharP.cast_eq_zero_iff Geom K1.p _).mp hz'))
    have hcoeff : (topHasse 1 f).coeff m ≠ 0 := by
      rw [topHasse_coeff, hm, hsum, Nat.choose_one_right]
      exact mul_ne_zero hc (MvPolynomial.mem_support_iff.mp hu)
    intro hz
    exact hcoeff (by rw [hz]; rfl)
  rintro ⟨g, hg⟩
  have hg0 : g ≠ 0 := by
    intro h
    exact hnz (by rw [hg, h, mul_zero])
  have h := MvPolynomial.degreeOf_mul_eq (n := (3 : Fin 4)) hf.ne_zero hg0
  rw [hg, h] at hdeg
  omega
theorem exists_divided_cut {P H f : Row 4} {k a l A : ℕ} (hP : P ≠ 0) (hH : H ≠ 0)
    (hf : Irreducible f) (htop : 0 < f.degreeOf 3) (hchar : f.degreeOf 3 < K1.p)
    (hc : IsRelPrime f H) (hl : l ≤ k-a)
    (hb : InBox (shape P) primaryBox) (hw : TrueWeightLE P primaryCutoff)
    (hactive : ActiveFits P A) (divH : H^k ∣ P) (divF : f^a ∣ P) (exactF : ¬ f^(a+1) ∣ P) :
    ∃ Q : Row 4, (¬ f ∣ Q) ∧ InBox (shape Q) (residualBox (shape H) l) ∧
      TrueWeightLE Q primaryCutoff ∧ ActiveFits Q A ∧
      ∀ S : (Polynomial Geom), atJet H S ≠ 0 → OrderAt P S k → OrderAt Q S l := by
  obtain ⟨G,rfl⟩ := divH
  have hn : G ≠ 0 := right_ne_zero_of_mul hP
  have hGb := residual_box (hl.trans (Nat.sub_le k a)) hH hn hb
  have hGw := weight_of_factor hP (dvd_mul_left G (H^k)) hw
  have hdiv : f^a ∣ G := hc.pow.dvd_of_dvd_mul_left divF
  have hnext : ¬ f^(a+1) ∣ G := fun hd => exactF (hd.trans (dvd_mul_left G _))
  have hnd := exact_hasse_not_dvd translateTop topHasse_zero f G a
    (UniqueFactorizationMonoid.irreducible_iff_prime.mp hf)
    (topHasse_one_not_dvd f hf htop hchar) hdiv hnext
  obtain ⟨boxQ,weightQ⟩ := topHasse_bounds _ _ a G hGb hGw
  have hactiveG : ActiveFits G A := (Final50GeoCover.activeFits_iff G A).mpr
    ((weightedTotalDegree_le_of_dvd _ (dvd_mul_left G (H^k)) hP).trans
      ((Final50GeoCover.activeFits_iff _ A).mp hactive))
  have hactiveQ : ActiveFits (topHasse a G) A := by
    intro m hm
    have hh := hactiveG _ (source_support hm)
    simp [Finsupp.add_apply] at hh
    omega
  refine ⟨topHasse a G,hnd,boxQ,weightQ,hactiveQ,?_⟩
  intro S hS hPS m hm
  have hor := orderAt_off_quotient hS hPS
  exact hl.trans (topHasse_order a k G S hor m hm)
theorem retained_power_dvd {ι : Type*} [Fintype ι] [DecidableEq ι] (z : Finset ι)
    (f : ι → Row 4) (hfi : ∀ i, Irreducible (f i))
    (hdis : ∀ i j, i ≠ j → ¬ Associated (f i) (f j))
    {P : Row 4} {k : ℕ} (hdiv : ∀ i ∈ z, f i ^ k ∣ P) : (∏ i ∈ z, f i)^k ∣ P := by
  rw [← Finset.prod_pow]
  apply Finset.prod_dvd_of_isRelPrime
  · intro i _ j _ hij
    exact ((hfi i).isRelPrime_iff_not_dvd.mpr
      (fun hd => hdis i j hij ((hfi i).associated_of_dvd (hfi j) hd))).pow
  · exact hdiv
theorem prime_off_product {ι : Type*} [DecidableEq ι] (z : Finset ι)
    (f : ι → Row 4) (hfi : ∀ i, Irreducible (f i))
    (hdis : ∀ i j, i ≠ j → ¬ Associated (f i) (f j))
    {i : ι} (hi : i ∉ z) : IsRelPrime (f i) (∏ j ∈ z, f j) := by
  apply IsRelPrime.prod_right
  intro j hj
  exact (hfi i).isRelPrime_iff_not_dvd.mpr
    (fun hd => hdis i j (fun eq => hi (eq ▸ hj)) ((hfi i).associated_of_dvd (hfi j) hd))
#print axioms residual_box
#print axioms exists_divided_cut
#print axioms retained_power_dvd
end
end Low6966RetainedCut

end Merged6967_Low6966RetainedWitness

section Merged6967_Low6966ShapeGate
set_option Elab.async false



set_option Elab.async false
set_option autoImplicit false

namespace Low6966ShapeGate

open K1_13_2 (cappedCount)
open K1_13_2_2 (JetExp oldWeight gradeWeight cumulativeExponents mem_cumulativeColumns)
open TaperColumns (jetColumns jetExponents)
open TaperMoments (gradeCap)
open scoped BigOperators
open Finset
open K1_13_2_2_3 (cappedColumns mem_cappedColumns capped_card)
open K1_13_2_2_3 (cappedColumns mem_cappedColumns capped_card)
open TaperColumns (sumGrade sumOld)

def fits (r : ℕ) (m : JetExp) : Prop :=
  m.weight gradeWeight ≤ r*62 ∧ m.weight oldWeight ≤ r*28 ∧ m 3 ≤ r*7

noncomputable instance (r : ℕ) (m : JetExp) : Decidable (fits r m) := by unfold fits; infer_instance

noncomputable def width (r : ℕ) : ℕ := (jetColumns.filter (fits r)).card

def bound (r : ℕ) : ℕ := min 4013 (r*62+1)
def start (k : ℕ) : ℕ := 16*k
def stop (r k : ℕ) : ℕ := min (bound r) (start (k+1))
def chunks (r : ℕ) : ℕ := (bound r + 15) / 16

def padGrade (r k : ℕ) : ℕ :=
  min (gradeCap (start k)) (gradeCap (stop r k-1))

def index (r : ℕ) : ℕ := min 1650 (r*28)

private theorem grade_le {r k q : ℕ} (hlo : start k ≤ q) (hhi : q < stop r k) :
    padGrade r k ≤ gradeCap q := by
  unfold padGrade gradeCap
  have hcap := TaperBudget.cap_antitone (show q ≤ stop r k-1 by omega)
  exact le_min ((min_le_left _ _).trans ((min_le_left _ _).trans hlo))
    ((min_le_right _ _).trans ((min_le_right _ _).trans hcap))

private noncomputable def grid (r : ℕ) : Finset (Σ _ : ℕ, ℕ × JetExp) :=
  (range (chunks r)).sigma fun k => (Ico (start k) (stop r k)).product
    (cappedColumns (padGrade r k) (index r) (r*7))

private noncomputable def pad (r : ℕ) (x : Σ _ : ℕ, ℕ × JetExp) : JetExp :=
  x.2.2 + Finsupp.single 0 (x.2.1 - padGrade r x.1)

private theorem pad_spec {r : ℕ} {x : Σ _ : ℕ, ℕ × JetExp} (hx : x ∈ grid r) :
    (pad r x).weight gradeWeight = x.2.1 ∧
    (pad r x).weight oldWeight = x.2.2.weight oldWeight ∧
    (∀ i : Fin 4, i ≠ 0 → pad r x i = x.2.2 i) := by
  obtain ⟨k,q,m⟩ := x
  have hm := (mem_cappedColumns.mp (mem_product.mp (mem_sigma.mp hx).2).2).1
  have hm' := (mem_cumulativeColumns.mp hm).1
  have hg : m.weight gradeWeight = padGrade r k := by exact_mod_cast hm'
  obtain ⟨hl,hh⟩ := mem_Ico.mp (mem_product.mp (mem_sigma.mp hx).2).1
  change start k ≤ q at hl
  change q < stop r k at hh
  have hq := (grade_le hl hh).trans (min_le_left _ _ : gradeCap q ≤ q)
  have h0 : pad r ⟨k,q,m⟩ 0 = m 0 + (q-padGrade r k) := by simp [pad]
  have hsucc (i : Fin 4) (hi : i ≠ 0) : pad r ⟨k,q,m⟩ i = m i := by
    simp [pad,Finsupp.single_eq_of_ne hi]
  refine ⟨?_, ?_, hsucc⟩
  · change (pad r ⟨k,q,m⟩).weight gradeWeight = q
    rw [sumGrade, h0, hsucc 1 (by decide), hsucc 2 (by decide), hsucc 3 (by decide)]
    rw [sumGrade] at hg
    omega
  · rw [sumOld,sumOld,hsucc 1 (by decide),hsucc 2 (by decide),hsucc 3 (by decide)]

private theorem map_mem {r : ℕ} {x : Σ _ : ℕ, ℕ × JetExp} (hx : x ∈ grid r) :
    pad r x ∈ jetColumns.filter (fits r) := by
  obtain ⟨k,q,m⟩ := x
  obtain ⟨hl,hh⟩ := mem_Ico.mp (mem_product.mp (mem_sigma.mp hx).2).1
  obtain ⟨hj,ht⟩ := mem_cappedColumns.mp (mem_product.mp (mem_sigma.mp hx).2).2
  obtain ⟨hg,hi⟩ := mem_cumulativeColumns.mp hj
  obtain ⟨eB,eJ,eOther⟩ := pad_spec hx
  dsimp only at eB eJ eOther hl hh
  have hgrade : m.weight gradeWeight = padGrade r k := by exact_mod_cast hg
  have hindex : m.weight oldWeight ≤ index r := by exact_mod_cast hi
  have htop : m 3 ≤ r*7 := by exact_mod_cast ht
  have hD := (grade_le hl hh).trans (min_le_right _ _ : gradeCap q ≤ TaperBudget.cap q)
  have hb : q ≤ 4012 ∧ q ≤ r*62 := by
    unfold stop bound at hh
    omega
  apply Finset.mem_filter.mpr
  refine ⟨?_,⟨eB.trans_le hb.2,eJ.trans_le (hindex.trans (min_le_right _ _)),?_⟩⟩
  · apply TaperColumns.jetExponents_finite.mem_toFinset.mpr
    change (pad r ⟨k,q,m⟩).weight gradeWeight ≤ 4012 ∧
      (pad r ⟨k,q,m⟩).weight oldWeight ≤ 1650 ∧ _
    refine ⟨eB.trans_le hb.1,eJ.trans_le (hindex.trans (min_le_left _ _)),?_⟩
    rw [eB,eOther 1 (by decide),eOther 2 (by decide),eOther 3 (by decide)]
    rw [sumGrade] at hgrade
    omega
  · rwa [eOther 3 (by decide)]

private theorem pad_injective (r : ℕ) : Set.InjOn (pad r) (grid r : Set (Σ _ : ℕ, ℕ × JetExp)) := by
  intro x hx y hy hxy
  obtain ⟨k,q,m⟩ := x
  obtain ⟨k',q',m'⟩ := y
  obtain ⟨hlo,hhi⟩ := mem_Ico.mp (mem_product.mp (mem_sigma.mp hx).2).1
  obtain ⟨hlo',hhi'⟩ := mem_Ico.mp (mem_product.mp (mem_sigma.mp hy).2).1
  have eQ : q = q' := (pad_spec hx).1.symm.trans ((congrArg (fun e : JetExp => e.weight gradeWeight) hxy).trans (pad_spec hy).1)
  subst q'
  have eK : k = k' := by
    change q < stop r k at hhi
    change q < stop r k' at hhi'
    change start k ≤ q at hlo
    change start k' ≤ q at hlo'
    simp only [stop, start] at hhi hhi' hlo hlo'
    omega
  subst k'
  have em : m = m' := by
    apply add_right_cancel (b := Finsupp.single (0 : Fin 4) (q-padGrade r k))
    exact hxy
  subst m'
  rfl

def block (r k : ℕ) : ℤ :=
  ((stop r k-start k : ℕ) : ℤ) * cappedCount (padGrade r k) (index r) (r*7)

def compute (r : ℕ) : ℤ := ∑ k ∈ range (chunks r), block r k

private theorem grid_eq (r : ℕ) : ((grid r).card : ℤ) = compute r := by
  unfold grid compute
  rw [card_sigma,Nat.cast_sum]
  apply sum_congr rfl
  intro k _
  change (((Ico (start k) (stop r k)).product
    (cappedColumns (padGrade r k) (index r) (r*7))).card : ℤ) = block r k
  have hcard := Finset.card_product (Ico (start k) (stop r k))
    (cappedColumns (padGrade r k) (index r) (r*7))
  change ((Ico (start k) (stop r k)).product
    (cappedColumns (padGrade r k) (index r) (r*7))).card = _ at hcard
  rw [hcard, Nat.card_Ico, Nat.cast_mul, capped_card K1_13_2_2_2.proof]
  rfl

theorem width_ge (r : ℕ) : compute r ≤ (width r : ℤ) := by
  rw [← grid_eq]
  exact_mod_cast Finset.card_le_card_of_injOn (pad r) (fun _ h => map_mem h) (pad_injective r)

private theorem jet_count : jetColumns.card = Low6966Prices.symbolCount := by
  exact_mod_cast TaperColumns.jet_card_eq.trans TaperColumns.sourceCount_eq

private theorem width_le (r : ℕ) : width r ≤ Low6966Prices.symbolCount := by
  rw [← jet_count]
  exact card_le_card (filter_subset _ _)

private theorem width_full (r : ℕ) (hr : 79 ≤ r) : width r = Low6966Prices.symbolCount := by
  unfold width
  rw [filter_true_of_mem, jet_count]
  intro m hm
  have h : m ∈ jetExponents := TaperColumns.jetExponents_finite.mem_toFinset.mp hm
  unfold fits
  have ht : 3*m 3 ≤ m.weight oldWeight := by rw [sumOld]; omega
  exact ⟨h.1.trans (by omega), h.2.1.trans (by omega), by have hJ := h.2.1; omega⟩

def intPrefix (f : ℕ → ℤ) : ℕ → ℤ
  | 0 => 0
  | n+1 => intPrefix f n + f n

theorem intPrefix_eq (f : ℕ → ℤ) (n : ℕ) :
    intPrefix f n = ∑ k ∈ range n, f k := by
  induction n with
  | zero => simp [intPrefix]
  | succ n ih => rw [intPrefix,sum_range_succ,ih]

def fastRow (r : ℕ) : ℤ := intPrefix (block r) (chunks r)

theorem fastRow_eq (r : ℕ) : fastRow r = compute r := intPrefix_eq _ _

def rowLoss (i : ℕ) : ℤ := (Low6966Prices.symbolCount : ℤ) - fastRow (i+1)

private theorem intPrefix_add (f : ℕ → ℤ) (a b : ℕ) :
    intPrefix f (a+b) = intPrefix f a + intPrefix (fun i => f (a+i)) b := by
  induction b with
  | zero => simp [intPrefix]
  | succ b ih => rw [Nat.add_succ, intPrefix, ih, intPrefix, add_assoc]

private theorem part0 : intPrefix (fun k => rowLoss (0+k)) 7 = 2847510389616 := by decide +kernel

private theorem part7 : intPrefix (fun k => rowLoss (7+k)) 7 = 2843953366070 := by decide +kernel

private theorem part14 : intPrefix (fun k => rowLoss (14+k)) 7 = 2824071789052 := by decide +kernel

private theorem part21 : intPrefix (fun k => rowLoss (21+k)) 7 = 2763124338860 := by decide +kernel

private theorem part28 : intPrefix (fun k => rowLoss (28+k)) 7 = 2624475471537 := by decide +kernel

private theorem part35 : intPrefix (fun k => rowLoss (35+k)) 7 = 2359595412955 := by decide +kernel

private theorem part42 : intPrefix (fun k => rowLoss (42+k)) 7 = 1908060169535 := by decide +kernel

private theorem part49 : intPrefix (fun k => rowLoss (49+k)) 7 = 1197551515315 := by decide +kernel

private theorem part56 : intPrefix (fun k => rowLoss (56+k)) 7 = 328796153027 := by decide +kernel

private theorem part63 : intPrefix (fun k => rowLoss (63+k)) 7 = 22729886625 := by decide +kernel

private theorem part70 : intPrefix (fun k => rowLoss (70+k)) 7 = 8349761869 := by decide +kernel

private theorem part77 : intPrefix (fun k => rowLoss (77+k)) 1 = 1058415011 := by decide +kernel

set_option maxRecDepth 10000 in
theorem computed_loss : intPrefix rowLoss 78 = Low6966SharedPrice.slopeLoss := by
  have h0 : intPrefix rowLoss 0 = 0 := rfl
  have h7 : intPrefix rowLoss 7 = 2847510389616 := by
    rw [show (7 : ℕ) = 0+7 by decide,intPrefix_add,h0,part0]
    rfl
  have h14 : intPrefix rowLoss 14 = 5691463755686 := by
    rw [show (14 : ℕ) = 7+7 by decide,intPrefix_add,h7,part7]
    rfl
  have h21 : intPrefix rowLoss 21 = 8515535544738 := by
    rw [show (21 : ℕ) = 14+7 by decide,intPrefix_add,h14,part14]
    rfl
  have h28 : intPrefix rowLoss 28 = 11278659883598 := by
    rw [show (28 : ℕ) = 21+7 by decide,intPrefix_add,h21,part21]
    rfl
  have h35 : intPrefix rowLoss 35 = 13903135355135 := by
    rw [show (35 : ℕ) = 28+7 by decide,intPrefix_add,h28,part28]
    rfl
  have h42 : intPrefix rowLoss 42 = 16262730768090 := by
    rw [show (42 : ℕ) = 35+7 by decide,intPrefix_add,h35,part35]
    rfl
  have h49 : intPrefix rowLoss 49 = 18170790937625 := by
    rw [show (49 : ℕ) = 42+7 by decide,intPrefix_add,h42,part42]
    rfl
  have h56 : intPrefix rowLoss 56 = 19368342452940 := by
    rw [show (56 : ℕ) = 49+7 by decide,intPrefix_add,h49,part49]
    rfl
  have h63 : intPrefix rowLoss 63 = 19697138605967 := by
    rw [show (63 : ℕ) = 56+7 by decide,intPrefix_add,h56,part56]
    rfl
  have h70 : intPrefix rowLoss 70 = 19719868492592 := by
    rw [show (70 : ℕ) = 63+7 by decide,intPrefix_add,h63,part63]
    rfl
  have h77 : intPrefix rowLoss 77 = 19728218254461 := by
    rw [show (77 : ℕ) = 70+7 by decide,intPrefix_add,h70,part70]
    rfl
  have h78 : intPrefix rowLoss 78 = 19729276669472 := by
    rw [show (78 : ℕ) = 77+1 by decide,intPrefix_add,h77,part77]
    rfl
  exact h78

theorem loss_bound (N : ℕ) :
    (∑ i ∈ range N, (Low6966Prices.symbolCount - width (i+1))) ≤ Low6966SharedPrice.slopeLoss := by
  let f : ℕ → ℕ := fun i => Low6966Prices.symbolCount - width (i+1)
  change (∑ i ∈ range N, f i) ≤ _
  have hzero (i : ℕ) (hi : 78 ≤ i) : f i = 0 := by
    dsimp [f]
    rw [width_full (i+1) (by omega),Nat.sub_self]
  rw [K1_13_8.sum_range_min N 78 hzero]
  refine (sum_le_sum_of_subset (range_mono (min_le_right N 78))).trans ?_
  have row (i : ℕ) : (f i : ℤ) ≤ rowLoss i := by
    unfold f rowLoss
    rw [Int.ofNat_sub (width_le _),fastRow_eq]
    exact sub_le_sub_left (width_ge (i+1)) _
  apply Int.ofNat_le.mp
  rw [Nat.cast_sum, ← computed_loss, intPrefix_eq]
  exact sum_le_sum fun i _ => row i

#print axioms loss_bound

end Low6966ShapeGate

end Merged6967_Low6966ShapeGate

section Merged6967_Low6966SharedPersistent
set_option Elab.async false


set_option Elab.async false

namespace Low6966SharedPersistent
noncomputable section

open P3 (K)
open K1_13 (Geom Row extend atJet shape InBox OrderAt)
open K1_13_6 (GeoJets toGeneric)
open K1_13_6_1_2 (hassePartial multiOrder VanishesTo hasse_inBox hasse_atJet_eq_zero map_hassePartial)
open MvPolynomial Polynomial

/-- Include every admissible-width row that vanishes at the marked messages. -/
def vanishing (Γ : Finset K) (s : K → (Polynomial K)) : Submodule Geom (Row 4) where
  carrier := {P | P.totalDegree ≤ 4012 ∧ ∀ γ ∈ Γ, atJet P (extend (s γ)) = 0}
  zero_mem' := ⟨by simp,fun _ _ => by simp [atJet]⟩
  add_mem' := by
    intro p q hp hq
    exact ⟨(totalDegree_add p q).trans (max_le hp.1 hq.1),fun γ hγ => by
      simp only [atJet, map_add]
      change atJet p (extend (s γ)) + atJet q (extend (s γ)) = 0
      rw [hp.2 γ hγ,hq.2 γ hγ,add_zero]⟩
  smul_mem' := by
    intro a p hp
    refine ⟨(totalDegree_smul_le a p).trans hp.1,fun γ hγ => ?_⟩
    change (MvPolynomial.eval _) (a • p) = 0
    rw [Algebra.smul_def, map_mul]
    change _ * atJet p (extend (s γ)) = 0
    rw [hp.2 γ hγ,mul_zero]

def Persistent (Γ : Finset K) (s : K → (Polynomial K)) (P : Ideal GeoJets) : Prop :=
  ∀ R ∈ vanishing Γ s, toGeneric R ∈ P

/-- Select one row for a finite set of nonpersistent surfaces. -/
theorem common_avoider (Γ : Finset K) (s : K → (Polynomial K)) (surfaces : Finset (Ideal GeoJets))
    (hZ : ∀ P ∈ surfaces, ¬ Persistent Γ s P) :
    ∃ R ∈ vanishing Γ s, ∀ P ∈ surfaces, toGeneric R ∉ P := by
  classical
  let M := vanishing Γ s
  let forbidden (P : surfaces) : Submodule Geom M :=
    ((P.val.comap (MvPolynomial.map K1_13_6.genericCoeffs) : Ideal (Row 4)).restrictScalars Geom).comap M.subtype
  have hproper (P : surfaces) : forbidden P ≠ ⊤ := by
    intro h
    apply hZ P.val P.property
    intro R hR
    have hmem : (⟨R,hR⟩ : M) ∈ forbidden P := h ▸ Submodule.mem_top
    exact hmem
  obtain ⟨R,hR⟩ := Submodule.exists_forall_notMem_of_forall_ne_top
    (ι := ↥surfaces) (K := Geom) (M := M) forbidden hproper
  exact ⟨R.val,R.property,fun P hP => hR ⟨P,hP⟩⟩

theorem derivative_mem {Γ s P R n} (hp : Persistent Γ s P)
    (hb : InBox (shape R) Low6966Prices.primaryBox)
    (ho : ∀ γ ∈ Γ, OrderAt R (extend (s γ)) n)
    (a : Fin 4 →₀ ℕ) (ha : multiOrder a < n) :
    hassePartial a (toGeneric R) ∈ P := by
  unfold toGeneric
  rw [← map_hassePartial]
  exact hp _ ⟨(hasse_inBox a hb).1,fun γ hγ => hasse_atJet_eq_zero ha (ho γ hγ)⟩

theorem local_order {Γ s R n} {P : Ideal GeoJets} [P.IsPrime] (hp : Persistent Γ s P)
    (hb : InBox (shape R) Low6966Prices.primaryBox)
    (ho : ∀ γ ∈ Γ, OrderAt R (extend (s γ)) n) : VanishesTo P (toGeneric R) n :=
  K1_13_6_1_2_2.vanishesTo_of_hasse _ P n (fun a ha => derivative_mem hp hb ho a ha)

#print axioms common_avoider
#print axioms local_order
end
end Low6966SharedPersistent

end Merged6967_Low6966SharedPersistent
