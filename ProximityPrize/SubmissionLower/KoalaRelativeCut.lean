import ProximityPrize.SubmissionLower.KoalaRuledEmbedding
import ProximityPrize.SubmissionLower.KoalaPointCount
import ProximityPrize.SubmissionLower.KoalaRectTaylorEval -- serialize candidate build

set_option autoImplicit false
set_option maxHeartbeats 900000

namespace SplitCut.Rect
noncomputable section

open MvPolynomial Filter

variable {F : Type} [Field F]

abbrev embedded (I : Ideal (Ring F)) (a b c : ℕ) :
    Ideal (MvPolynomial (diagonal a b c 1).support F) := I.comap (project F a b c)

/-- Relative sections lose one ordinary affine dimension on the diagonal embedding.
    This applies to the graph's first cut and to all proper cuts of the resulting curves. -/
theorem relative_cut_coeff {I J : Ideal (Ring F)} (hIJ : I ≤ J)
    {a b c q : ℕ} (ha : 0 < a) (S : Section I (diagonal a b c q)) (hS : S.finite ∈ J)
    (hreg : IsLeftRegular (Ideal.Quotient.mk I S.finite)) :
    let P := affineHilbertPolynomial (embedded I a b c)
    let Q := affineHilbertPolynomial (embedded J a b c)
    Q.natDegree ≤ P.natDegree - 1 ∧ Q.coeff (P.natDegree-1) ≤ q*P.natDegree*P.leadingCoeff := by
  let I' := embedded I a b c
  let J' := embedded J a b c
  let P := affineHilbertPolynomial I'
  let Q := affineHilbertPolynomial J'
  apply Polynomial.natDegree_le_and_coeff_le_of_eventually_eval_natCast_le_backwardDifference
    (eventually_eval_affineHilbertPolynomial_nonneg J')
  obtain ⟨N, hN⟩ := exists_eval_affineHilbertPolynomial I'
  filter_upwards [eventually_eval_affineHilbertPolynomial J',
    eventually_ge_atTop (N+q+2*S.order)] with n hn ht
  have hq : q ≤ n := by omega
  have he : (diagonal a b c (n-q)).add (diagonal a b c q) = diagonal a b c n := by
    simp only [diagonal, Box.add, ← Nat.mul_add, Nat.sub_add_cancel hq]
  have hpad : 2*S.order ≤ (diagonal a b c (n-q)).base :=
    (show 2*S.order ≤ n-q by omega).trans (Nat.le_mul_of_pos_left _ ha)
  have hdrop := hilbert_drop hIJ S hpad hS hreg
  rw [he, ← diagonal_piece J, ← diagonal_piece I, ← diagonal_piece I] at hdrop
  have hq' := Nat.cast_le (α:=ℚ).mpr hdrop
  push_cast at hq'
  change Q.eval (n:ℚ) ≤ (Polynomial.backwardDifference (q:ℚ) P).eval (n:ℚ)
  rw [Polynomial.eval_backwardDifference, ← Nat.cast_sub hq, hn, hN n (by omega),
    hN (n-q) (by omega)]
  linarith only [hq']

/-- A proper relative section of a degree-one component bounds marked points. -/
theorem relative_cut_points {I J : Ideal (Ring F)} [I.IsPrime] (hIJ : I ≤ J)
    {a b c q : ℕ} (ha : 0 < a) (S : Section I (diagonal a b c q)) (hS : S.finite ∈ J)
    (hproper : S.finite ∉ I) (hcurve : (affineHilbertPolynomial (embedded I a b c)).natDegree = 1)
    {α E : Type} [Field E] [Algebra F E] (T : Finset α)
    (x : α → (diagonal a b c 1).support → E) (hinj : Set.InjOn x (T : Set α))
    (hT : ∀ i ∈ T, x i ∈ zeroLocus E (embedded J a b c)) :
    (T.card : ℚ) ≤ q*affineDegree (embedded I a b c) := by
  classical
  have hreg : IsLeftRegular (Ideal.Quotient.mk I S.finite) :=
    IsLeftCancelMulZero.mul_left_cancel_of_ne_zero (mt Ideal.Quotient.eq_zero_iff_mem.mp hproper)
  have h := relative_cut_coeff hIJ ha S hS hreg
  simp only [hcurve, Nat.sub_self, Nat.cast_one, mul_one] at h
  have hd : (affineHilbertPolynomial (embedded J a b c)).natDegree = 0 := Nat.eq_zero_of_le_zero h.1
  obtain ⟨hfinite, hcard⟩ := finite_zeroLocus_and_ncard_le_affineDegree (K:=E) _ hd
  have hsub : (T.image x : Set ((diagonal a b c 1).support → E)) ⊆
      zeroLocus E (embedded J a b c) := by
    intro y hy
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hy
    exact hT i hi
  have hle := Set.ncard_le_ncard hsub hfinite
  rw [Set.ncard_coe_finset, Finset.card_image_of_injOn hinj] at hle
  refine ((Nat.cast_le (α:=ℚ).mpr hle).trans hcard).trans ?_
  simp only [affineDegree, hd, Nat.factorial_zero, Nat.cast_one, one_mul,
    Polynomial.leadingCoeff, hcurve, Nat.factorial_one]
  simpa only [Polynomial.leadingCoeff, hcurve] using h.2

end
end SplitCut.Rect
