import ProximityPrize.SubmissionLower.BCHKSPolynomialPairDeterminantSpan6400

/-!
# Dimension forces degree descent in an unequal rank-one pair box

Suppose a finite-dimensional space of polynomial pairs has one fixed
coprime direction `(A,B)`, with every pair equal to a polynomial multiple of
that direction.  If `B` is nonzero and the second component has degree below
`h`, then all multipliers lie in the window of degrees below
`h - deg(B)`.  Projection to the second component is injective, so the whole
space has dimension at most that window.

This is the abstract algebraic core needed to convert score-64 locator-kernel
nullity into a sharper bound on the primitive Frobenius direction.
-/

namespace ProximityPrize.SubmissionLower
namespace BCHKSRankOneDimensionDegree6400

open Polynomial

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 3000000

variable {F : Type} [Field F]

/-- Projection of a polynomial-pair subspace to its second polynomial. -/
noncomputable def pairSecondPolynomialProjection
    {c h : Nat} (V : Submodule F (PolynomialPairSpace F c h)) :
    V →ₗ[F] F[X] where
  toFun v := v.1.2.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Multiplication by a fixed polynomial on a finite degree window. -/
noncomputable def multiplyFromDegreeWindow
    (B : F[X]) (r : Nat) : Polynomial.degreeLT F r →ₗ[F] F[X] where
  toFun M := M.1 * B
  map_add' M N := by simp only [Submodule.coe_add, add_mul]
  map_smul' a M := by simp

/-- If `M*B` has degree below `h`, then `M` lies in the complementary degree
window below `h-deg(B)`.  The zero multiplier is included explicitly. -/
theorem multiplier_mem_degreeLT_of_product_mem
    {h : Nat} (B M C : F[X])
    (hB : B ≠ 0) (hBdegree : B.natDegree < h)
    (hCdegree : C ∈ Polynomial.degreeLT F h)
    (hfactor : C = M * B) :
    M ∈ Polynomial.degreeLT F (h - B.natDegree) := by
  rw [Polynomial.mem_degreeLT]
  by_cases hM : M = 0
  · simp [hM]
  · have hC : C ≠ 0 := by
      rw [hfactor]
      exact mul_ne_zero hM hB
    have hCnat : C.natDegree < h :=
      (Polynomial.natDegree_lt_iff_degree_lt hC).2
        (Polynomial.mem_degreeLT.mp hCdegree)
    rw [hfactor, Polynomial.natDegree_mul hM hB] at hCnat
    have hMnat : M.natDegree < h - B.natDegree := by omega
    exact (Polynomial.natDegree_lt_iff_degree_lt hM).1 hMnat

/-- A linear injection whose image factors through multiplication from an
`r`-dimensional polynomial window has source dimension at most `r`. -/
theorem finrank_le_of_projection_factors_through_degreeWindow
    {c h r : Nat}
    (V : Submodule F (PolynomialPairSpace F c h))
    (proj : V →ₗ[F] F[X]) (B : F[X])
    (hinjective : Function.Injective proj)
    (hfactor : ∀ v : V, ∃ M : Polynomial.degreeLT F r,
      proj v = M.1 * B) :
    Module.finrank F V ≤ r := by
  have hrange : LinearMap.range proj ≤
      LinearMap.range (multiplyFromDegreeWindow B r) := by
    intro C hC
    rcases hC with ⟨v, rfl⟩
    rcases hfactor v with ⟨M, hM⟩
    exact ⟨M, hM.symm⟩
  have hprojdim := LinearMap.finrank_range_of_inj hinjective
  calc
    Module.finrank F V = Module.finrank F (LinearMap.range proj) :=
      hprojdim.symm
    _ ≤ Module.finrank F
          (LinearMap.range (multiplyFromDegreeWindow B r)) :=
      Submodule.finrank_mono hrange
    _ ≤ Module.finrank F (Polynomial.degreeLT F r) :=
      LinearMap.finrank_range_le (multiplyFromDegreeWindow B r)
    _ = r := by
      rw [Module.finrank_eq_card_basis (Polynomial.degreeLT.basis F r)]
      simp

/-- Common polynomial factorization through a nonzero second direction makes
second projection injective. -/
theorem pairSecondPolynomialProjection_injective
    {c h : Nat} (V : Submodule F (PolynomialPairSpace F c h))
    (A B : F[X]) (hB : B ≠ 0)
    (hfactor : ∀ v : V, ∃ M : F[X],
      v.1.1.1 = M * A ∧ v.1.2.1 = M * B) :
    Function.Injective (pairSecondPolynomialProjection V) := by
  intro v w hvw
  change v.1.2.1 = w.1.2.1 at hvw
  obtain ⟨M, hvA, hvB⟩ := hfactor v
  obtain ⟨N, hwA, hwB⟩ := hfactor w
  have hMN : M = N := by
    apply mul_right_cancel₀ hB
    exact hvB.symm.trans (hvw.trans hwB)
  apply Subtype.ext
  apply Prod.ext
  · apply Subtype.ext
    rw [hvA, hwA, hMN]
  · apply Subtype.ext
    exact hvw

/-- Dimension bound for a polynomial-pair space with a fixed nonzero
polynomial direction. -/
theorem finrank_le_secondDirection_window
    {c h : Nat} (V : Submodule F (PolynomialPairSpace F c h))
    (A B : F[X]) (hB : B ≠ 0) (hBdegree : B.natDegree < h)
    (hfactor : ∀ v : V, ∃ M : F[X],
      v.1.1.1 = M * A ∧ v.1.2.1 = M * B) :
    Module.finrank F V ≤ h - B.natDegree := by
  apply finrank_le_of_projection_factors_through_degreeWindow
    V (pairSecondPolynomialProjection V) B
  · exact pairSecondPolynomialProjection_injective V A B hB hfactor
  · intro v
    obtain ⟨M, _hA, hM⟩ := hfactor v
    refine ⟨⟨M, ?_⟩, hM⟩
    exact multiplier_mem_degreeLT_of_product_mem B M v.1.2.1
      hB hBdegree v.1.2.2 hM

/-- Coprimality upgrades a rational rank-one cross relation to the polynomial
factorization needed by the dimension argument. -/
theorem secondDirection_natDegree_le_sub_finrank_of_coprime_cross
    {c h : Nat} (V : Submodule F (PolynomialPairSpace F c h))
    (A B : F[X]) (hA : A ≠ 0) (hB : B ≠ 0)
    (hcoprime : IsCoprime A B) (hBdegree : B.natDegree < h)
    (hcross : ∀ v : V,
      A * v.1.2.1 = B * v.1.1.1) :
    B.natDegree ≤ h - Module.finrank F V := by
  have hfactor : ∀ v : V, ∃ M : F[X],
      v.1.1.1 = M * A ∧ v.1.2.1 = M * B := by
    intro v
    exact exists_polynomial_multiplier_of_coprime_cross
      A B v.1.1.1 v.1.2.1 hA hcoprime (hcross v)
  have hdim := finrank_le_secondDirection_window
    V A B hB hBdegree hfactor
  omega

/-- Symmetric form requiring only the second direction to be nonzero.  This
also covers the temporary one-lane case `A=0`; swapping the coprime-cross
factorization still produces the same common multiplier. -/
theorem secondDirection_natDegree_le_sub_finrank_of_coprime_cross'
    {c h : Nat} (V : Submodule F (PolynomialPairSpace F c h))
    (A B : F[X]) (hB : B ≠ 0)
    (hcoprime : IsCoprime A B) (hBdegree : B.natDegree < h)
    (hcross : ∀ v : V,
      A * v.1.2.1 = B * v.1.1.1) :
    B.natDegree ≤ h - Module.finrank F V := by
  have hfactor : ∀ v : V, ∃ M : F[X],
      v.1.1.1 = M * A ∧ v.1.2.1 = M * B := by
    intro v
    obtain ⟨M, hsecond, hfirst⟩ :=
      exists_polynomial_multiplier_of_coprime_cross
        B A v.1.2.1 v.1.1.1 hB hcoprime.symm (hcross v).symm
    exact ⟨M, hfirst, hsecond⟩
  have hdim := finrank_le_secondDirection_window
    V A B hB hBdegree hfactor
  omega

/-- A nonzero common factor in one pivot does not affect the dimension
rebate: pairwise determinant zero lets it cancel before applying the coprime
direction theorem. -/
theorem secondDirection_natDegree_le_sub_finrank_of_factored_pivot
    {c h : Nat} (V : Submodule F (PolynomialPairSpace F c h))
    (pivot : V) (H A B : F[X])
    (hH : H ≠ 0) (hB : B ≠ 0)
    (hcoprime : IsCoprime A B) (hBdegree : B.natDegree < h)
    (hpivotA : pivot.1.1.1 = H * A)
    (hpivotB : pivot.1.2.1 = H * B)
    (hdet : ∀ v : V, polynomialPairDet v.1 pivot.1 = 0) :
    B.natDegree ≤ h - Module.finrank F V := by
  have hcross : ∀ v : V,
      A * v.1.2.1 = B * v.1.1.1 := by
    intro v
    have hdet' :
        v.1.1.1 * (H * B) - v.1.2.1 * (H * A) = 0 := by
      simpa only [polynomialPairDet, hpivotA, hpivotB] using hdet v
    have hproduct :
        H * (v.1.1.1 * B - v.1.2.1 * A) = 0 := by
      calc
        H * (v.1.1.1 * B - v.1.2.1 * A) =
            v.1.1.1 * (H * B) - v.1.2.1 * (H * A) := by ring
        _ = 0 := hdet'
    have hinner : v.1.1.1 * B - v.1.2.1 * A = 0 :=
      (mul_eq_zero.mp hproduct).resolve_left hH
    have heq := sub_eq_zero.mp hinner
    calc
      A * v.1.2.1 = v.1.2.1 * A := mul_comm _ _
      _ = v.1.1.1 * B := heq.symm
      _ = B * v.1.1.1 := mul_comm _ _
  exact secondDirection_natDegree_le_sub_finrank_of_coprime_cross'
    V A B hB hcoprime hBdegree hcross

/-- Finite-family wrapper.  Linear independence identifies the span
dimension with the family cardinality, while bilinearity propagates the
pairwise determinant identities to the whole span. -/
theorem secondDirection_natDegree_le_sub_card_of_factored_member
    {I : Type} [Fintype I] {c h : Nat}
    (family : I → PolynomialPairSpace F c h)
    (hLI : LinearIndependent F family) (j : I)
    (H A B : F[X]) (hH : H ≠ 0) (hB : B ≠ 0)
    (hcoprime : IsCoprime A B) (hBdegree : B.natDegree < h)
    (hpivotA : (family j).1.1 = H * A)
    (hpivotB : (family j).2.1 = H * B)
    (hdet : ∀ i k, polynomialPairDet (family i) (family k) = 0) :
    B.natDegree ≤ h - Fintype.card I := by
  let V := Submodule.span F (Set.range family)
  let pivot : V :=
    ⟨family j, Submodule.subset_span (Set.mem_range_self j)⟩
  have hVrank : Module.finrank F V = Fintype.card I := by
    simpa only [V] using finrank_span_eq_card hLI
  have hdetV : ∀ v : V, polynomialPairDet v.1 pivot.1 = 0 := by
    intro v
    refine Submodule.span_induction (p := fun x _ ↦
      polynomialPairDet x (family j) = 0) ?_ ?_ ?_ ?_ v.2
    · intro x hx
      rcases hx with ⟨i, rfl⟩
      exact hdet i j
    · exact polynomialPairDet_zero_left (family j)
    · intro x y _hx _hy hxdet hydet
      simpa only [polynomialPairDet_add_left, hxdet, hydet, add_zero]
    · intro a x _hx hxdet
      simpa only [polynomialPairDet_smul_left, hxdet, smul_zero]
  have hbound :=
    secondDirection_natDegree_le_sub_finrank_of_factored_pivot
      V pivot H A B hH hB hcoprime hBdegree
        (by simpa only [pivot] using hpivotA)
        (by simpa only [pivot] using hpivotB) hdetV
  rwa [hVrank] at hbound

end BCHKSRankOneDimensionDegree6400
end ProximityPrize.SubmissionLower
