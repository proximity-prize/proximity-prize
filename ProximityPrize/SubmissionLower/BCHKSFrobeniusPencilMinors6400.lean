import ProximityPrize.SubmissionLower.BCHKSFrobeniusSourceMatrix6400
import Mathlib.LinearAlgebra.Matrix.Polynomial

/-!
# Affine pencil minors for the low-stack source matrix

Only the second block of `h` columns depends on the pencil parameter.  This
module records the resulting degree-`h` determinant bound and identifies the
constant and top coefficients.
-/

namespace ProximityPrize.SubmissionLower

open Polynomial
open scoped BigOperators

variable {K : Type} [Field K]

/-- An injective map identifies a finite set with its finite image. -/
noncomputable def finsetImageEquivOfInjective
    {A B : Type} [DecidableEq B] (S : Finset A) (f : A → B)
    (hf : Function.Injective f) : S ≃ S.image f :=
  Equiv.ofBijective
    (fun x : S ↦ ⟨f x.1, Finset.mem_image.mpr ⟨x.1, x.2, rfl⟩⟩)
    ⟨by
      intro x y hxy
      apply Subtype.ext
      apply hf
      exact congrArg Subtype.val hxy,
    by
      intro y
      rcases Finset.mem_image.mp y.2 with ⟨x, hx, hxy⟩
      refine ⟨⟨x, hx⟩, Subtype.ext ?_⟩
      exact hxy
    ⟩

/-- A square polynomial pencil in which only the right block of columns
depends on `X`. -/
noncomputable def rightColumnPencil
    {I J : Type} [Fintype I] [Fintype J]
    (base slope : Matrix (I ⊕ J) (I ⊕ J) K) :
    Matrix (I ⊕ J) (I ⊕ J) K[X]
  | r, Sum.inl i => Polynomial.C (base r (Sum.inl i))
  | r, Sum.inr j => Polynomial.C (base r (Sum.inr j)) +
      Polynomial.X * Polynomial.C (slope r (Sum.inr j))

/-- The matrix obtained by taking the constant left columns and the slope of
every right column. -/
def rightColumnLeadingMatrix
    {I J : Type} [Fintype I] [Fintype J]
    (base slope : Matrix (I ⊕ J) (I ⊕ J) K) :
    Matrix (I ⊕ J) (I ⊕ J) K
  | r, Sum.inl i => base r (Sum.inl i)
  | r, Sum.inr j => slope r (Sum.inr j)

/-- Evaluation of a right-column pencil in a target field. -/
def rightColumnSpecialization
    {I J L : Type} [Fintype I] [Fintype J] [Field L]
    (f : K →+* L) (w : L)
    (base slope : Matrix (I ⊕ J) (I ⊕ J) K) :
    Matrix (I ⊕ J) (I ⊕ J) L
  | r, Sum.inl i => f (base r (Sum.inl i))
  | r, Sum.inr j => f (base r (Sum.inr j)) +
      w * f (slope r (Sum.inr j))

/-- Since just the right block is affine in `X`, the determinant degree is at
most the number of right columns. -/
theorem natDegree_det_rightColumnPencil_le
    {I J : Type} [Fintype I] [Fintype J] [DecidableEq (I ⊕ J)]
    (base slope : Matrix (I ⊕ J) (I ⊕ J) K) :
    (rightColumnPencil base slope).det.natDegree ≤ Fintype.card J := by
  classical
  rw [Matrix.det_apply]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro σ hσ
  refine (Polynomial.natDegree_smul_le _ _).trans ?_
  rw [Fintype.prod_sum_type]
  refine Polynomial.natDegree_mul_le.trans ?_
  have hleft :
      (∏ i : I,
        rightColumnPencil base slope (σ (Sum.inl i)) (Sum.inl i)).natDegree ≤ 0 := by
    refine (Polynomial.natDegree_prod_le Finset.univ _).trans ?_
    simp [rightColumnPencil]
  have hright :
      (∏ j : J,
        rightColumnPencil base slope (σ (Sum.inr j)) (Sum.inr j)).natDegree ≤
        Fintype.card J := by
    refine (Polynomial.natDegree_prod_le Finset.univ _).trans ?_
    calc
      (∑ j : J, (rightColumnPencil base slope
          (σ (Sum.inr j)) (Sum.inr j)).natDegree) ≤ ∑ _j : J, 1 := by
            apply Finset.sum_le_sum
            intro j hj
            simp only [rightColumnPencil]
            compute_degree
      _ = Fintype.card J := by simp
  omega

/-- The constant coefficient of the right-column pencil determinant is the
determinant of the base matrix. -/
theorem coeff_det_rightColumnPencil_zero
    {I J : Type} [Fintype I] [Fintype J] [DecidableEq (I ⊕ J)]
    (base slope : Matrix (I ⊕ J) (I ⊕ J) K) :
    (rightColumnPencil base slope).det.coeff 0 = base.det := by
  classical
  rw [Matrix.det_apply, Matrix.det_apply, Polynomial.finsetSum_coeff]
  apply Finset.sum_congr rfl
  intro σ hσ
  rw [Polynomial.coeff_smul, Polynomial.coeff_zero_prod]
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  cases j <;> simp [rightColumnPencil]

/-- The coefficient at the full right-block degree takes the slope term from
every right column and the base term from every left column. -/
theorem coeff_det_rightColumnPencil_card
    {I J : Type} [Fintype I] [Fintype J] [DecidableEq (I ⊕ J)]
    (base slope : Matrix (I ⊕ J) (I ⊕ J) K) :
    (rightColumnPencil base slope).det.coeff (Fintype.card J) =
      (rightColumnLeadingMatrix base slope).det := by
  classical
  rw [Matrix.det_apply, Matrix.det_apply, Polynomial.finsetSum_coeff]
  apply Finset.sum_congr rfl
  intro σ hσ
  rw [Polynomial.coeff_smul]
  congr 1
  rw [Fintype.prod_sum_type, Fintype.prod_sum_type]
  simp only [rightColumnPencil, rightColumnLeadingMatrix]
  rw [← map_prod, Polynomial.coeff_C_mul]
  congr 1
  have hcoeff := Polynomial.coeff_prod_of_natDegree_le
    (s := (Finset.univ : Finset J))
    (fun j : J ↦ Polynomial.C (base (σ (Sum.inr j)) (Sum.inr j)) +
      Polynomial.X * Polynomial.C (slope (σ (Sum.inr j)) (Sum.inr j)))
    1 (by
      intro j hj
      compute_degree)
  simpa using hcoeff

/-- Determinant commutes with evaluating the pencil parameter in any target
field. -/
theorem eval₂_det_rightColumnPencil
    {I J L : Type} [Fintype I] [Fintype J] [DecidableEq (I ⊕ J)] [Field L]
    (f : K →+* L) (w : L)
    (base slope : Matrix (I ⊕ J) (I ⊕ J) K) :
    Polynomial.eval₂ f w (rightColumnPencil base slope).det =
      (rightColumnSpecialization f w base slope).det := by
  classical
  rw [← Polynomial.coe_eval₂RingHom, RingHom.map_det]
  congr 1
  ext r j
  cases j <;> (simp [rightColumnPencil, rightColumnSpecialization] <;> ring)

/-- The determinant polynomial of a selected full-column low-stack minor. -/
noncomputable def lowStackPencilMinor
    (S : Finset K) (source target₀ target₁ : K → K) (h : ℕ)
    (e : LowStackIndex h → S) : K[X] :=
  (rightColumnPencil
    ((lowStackMatrix S source target₀ h).submatrix e id)
    ((lowStackMatrix S source target₁ h).submatrix e id)).det

/-- A selected low-stack pencil minor has parameter degree at most `h`. -/
theorem lowStackPencilMinor_natDegree_le
    (S : Finset K) (source target₀ target₁ : K → K) (h : ℕ)
    (e : LowStackIndex h → S) :
    (lowStackPencilMinor S source target₀ target₁ h e).natDegree ≤ h := by
  simpa only [lowStackPencilMinor, Fintype.card_fin] using
    natDegree_det_rightColumnPencil_le
      ((lowStackMatrix S source target₀ h).submatrix e id)
      ((lowStackMatrix S source target₁ h).submatrix e id)

/-- The constant coefficient is the selected target-0 minor. -/
theorem lowStackPencilMinor_coeff_zero
    (S : Finset K) (source target₀ target₁ : K → K) (h : ℕ)
    (e : LowStackIndex h → S) :
    (lowStackPencilMinor S source target₀ target₁ h e).coeff 0 =
      ((lowStackMatrix S source target₀ h).submatrix e id).det := by
  exact coeff_det_rightColumnPencil_zero _ _

/-- The coefficient of degree `h` is the selected target-1 minor. -/
theorem lowStackPencilMinor_coeff_h
    (S : Finset K) (source target₀ target₁ : K → K) (h : ℕ)
    (e : LowStackIndex h → S) :
    (lowStackPencilMinor S source target₀ target₁ h e).coeff h =
      ((lowStackMatrix S source target₁ h).submatrix e id).det := by
  unfold lowStackPencilMinor
  have hcoeff :
      (rightColumnPencil
        ((lowStackMatrix S source target₀ h).submatrix e id)
        ((lowStackMatrix S source target₁ h).submatrix e id)).det.coeff h =
        (rightColumnLeadingMatrix
          ((lowStackMatrix S source target₀ h).submatrix e id)
          ((lowStackMatrix S source target₁ h).submatrix e id)).det := by
    simpa only [Fintype.card_fin] using
      (coeff_det_rightColumnPencil_card
        ((lowStackMatrix S source target₀ h).submatrix e id)
        ((lowStackMatrix S source target₁ h).submatrix e id))
  rw [hcoeff]
  congr 1
  ext r j
  cases j <;> rfl

/-- Evaluating a selected determinant polynomial gives the corresponding
minor of the specialized low-stack matrix. -/
theorem lowStackPencilMinor_eval
    (S : Finset K) (source target₀ target₁ : K → K) (h : ℕ)
    (e : LowStackIndex h → S) (w : K) :
    (lowStackPencilMinor S source target₀ target₁ h e).eval w =
      ((lowStackMatrix S source
        (fun x ↦ target₀ x + w * target₁ x) h).submatrix e id).det := by
  rw [lowStackPencilMinor, ← Polynomial.eval₂_id]
  rw [eval₂_det_rightColumnPencil]
  congr 1
  ext r j
  cases j <;> simp [rightColumnSpecialization, lowStackMatrix]
  ring

/-- More than `h` singular affine specializations force a selected pencil
minor polynomial to vanish identically. -/
theorem lowStackPencilMinor_eq_zero_of_many_kernels
    (S T : Finset K) (source target₀ target₁ : K → K) (h : ℕ)
    (e : LowStackIndex h → S)
    (hcard : h < T.card)
    (hkernels : ∀ w ∈ T,
      LinearMap.ker (lowStackRelationMap S source
        (fun x ↦ target₀ x + w * target₁ x) h) ≠ ⊥) :
    lowStackPencilMinor S source target₀ target₁ h e = 0 := by
  apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero'
    (lowStackPencilMinor S source target₀ target₁ h e) T
  · intro w hw
    rw [lowStackPencilMinor_eval]
    exact all_lowStack_maximal_minors_zero_of_ker_ne_bot
      S source (fun x ↦ target₀ x + w * target₁ x) h
      (hkernels w hw) e
  · exact (lowStackPencilMinor_natDegree_le
      S source target₀ target₁ h e).trans_lt hcard

/-- Many singular affine members force both endpoint low-stack matrices to
have nontrivial kernels.  The second endpoint comes from the coefficient of
degree `h`, not from an unjustified affine specialization at infinity. -/
theorem lowStack_endpoint_kernels_of_many_affine_kernels
    (S T : Finset K) (source target₀ target₁ : K → K) (h : ℕ)
    (hcard : h < T.card)
    (hkernels : ∀ w ∈ T,
      LinearMap.ker (lowStackRelationMap S source
        (fun x ↦ target₀ x + w * target₁ x) h) ≠ ⊥) :
    LinearMap.ker (lowStackRelationMap S source target₀ h) ≠ ⊥ ∧
      LinearMap.ker (lowStackRelationMap S source target₁ h) ≠ ⊥ := by
  constructor
  · apply lowStackRelationMap_ker_ne_bot_of_all_maximal_minors_zero
    intro e he
    have hzero := lowStackPencilMinor_eq_zero_of_many_kernels
      S T source target₀ target₁ h e hcard hkernels
    have hcoeff := congrArg (fun P : K[X] ↦ P.coeff 0) hzero
    simpa only [lowStackPencilMinor_coeff_zero, Polynomial.coeff_zero] using hcoeff
  · apply lowStackRelationMap_ker_ne_bot_of_all_maximal_minors_zero
    intro e he
    have hzero := lowStackPencilMinor_eq_zero_of_many_kernels
      S T source target₀ target₁ h e hcard hkernels
    have hcoeff := congrArg (fun P : K[X] ↦ P.coeff h) hzero
    simpa only [lowStackPencilMinor_coeff_h, Polynomial.coeff_zero] using hcoeff

/-- The same vanishing determinant polynomials give the generic kernel over
`F(W)`.  Rows are transported along the injective coefficient embedding. -/
theorem lowStack_generic_kernel_of_many_affine_kernels
    {F : Type} [Field F] [DecidableEq F] [DecidableEq (RatFunc F)]
    (S T : Finset F) (source target₀ target₁ : F → F)
    (genericSource genericTarget : RatFunc F → RatFunc F) (h : ℕ)
    (hcard : h < T.card)
    (hgenericSource : ∀ x ∈ S,
      genericSource (algebraMap F (RatFunc F) x) =
        algebraMap F (RatFunc F) (source x))
    (hgenericTarget : ∀ x ∈ S,
      genericTarget (algebraMap F (RatFunc F) x) =
        algebraMap F (RatFunc F) (target₀ x) +
          (RatFunc.X : RatFunc F) *
            algebraMap F (RatFunc F) (target₁ x))
    (hkernels : ∀ w ∈ T,
      LinearMap.ker (lowStackRelationMap S source
        (fun x ↦ target₀ x + w * target₁ x) h) ≠ ⊥) :
    LinearMap.ker
      (lowStackRelationMap
        (S.image (algebraMap F (RatFunc F)))
        genericSource genericTarget h) ≠ ⊥ := by
  classical
  let φ : F →+* RatFunc F := algebraMap F (RatFunc F)
  let E : S ≃ S.image φ :=
    finsetImageEquivOfInjective S φ φ.injective
  apply lowStackRelationMap_ker_ne_bot_of_all_maximal_minors_zero
  intro eg heg
  let e : LowStackIndex h → S := E.symm ∘ eg
  have heq (r : LowStackIndex h) : φ (e r).1 = (eg r).1 := by
    change (E (E.symm (eg r))).1 = (eg r).1
    exact congrArg Subtype.val (E.apply_symm_apply (eg r))
  have hPzero := lowStackPencilMinor_eq_zero_of_many_kernels
    S T source target₀ target₁ h e hcard hkernels
  have hspecialized :
      (rightColumnSpecialization φ (RatFunc.X : RatFunc F)
        ((lowStackMatrix S source target₀ h).submatrix e id)
        ((lowStackMatrix S source target₁ h).submatrix e id)).det = 0 := by
    rw [← eval₂_det_rightColumnPencil]
    change Polynomial.eval₂ φ (RatFunc.X : RatFunc F)
      (lowStackPencilMinor S source target₀ target₁ h e) = 0
    rw [hPzero]
    simp
  have hmatrix :
      (lowStackMatrix
        (S.image (algebraMap F (RatFunc F)))
        genericSource genericTarget h).submatrix eg id =
      rightColumnSpecialization φ (RatFunc.X : RatFunc F)
        ((lowStackMatrix S source target₀ h).submatrix e id)
        ((lowStackMatrix S source target₁ h).submatrix e id) := by
    ext r j
    cases j with
    | inl i =>
        simp only [Matrix.submatrix_apply, id_eq,
          lowStackMatrix, rightColumnSpecialization]
        rw [← heq r, hgenericSource (e r).1 (e r).2]
        simp only [map_pow, map_mul]
        rfl
    | inr i =>
        simp only [Matrix.submatrix_apply, id_eq,
          lowStackMatrix, rightColumnSpecialization]
        rw [← heq r, hgenericTarget (e r).1 (e r).2]
        simp only [map_pow, map_mul]
        dsimp only [φ]
        ring
  rw [hmatrix]
  exact hspecialized

/-- The full affine-pencil conclusion: the generic member and both projective
endpoints have nontrivial bounded kernels. -/
theorem lowStack_three_kernels_of_many_affine_kernels
    {F : Type} [Field F] [DecidableEq F] [DecidableEq (RatFunc F)]
    (S T : Finset F) (source target₀ target₁ : F → F)
    (genericSource genericTarget : RatFunc F → RatFunc F) (h : ℕ)
    (hcard : h < T.card)
    (hgenericSource : ∀ x ∈ S,
      genericSource (algebraMap F (RatFunc F) x) =
        algebraMap F (RatFunc F) (source x))
    (hgenericTarget : ∀ x ∈ S,
      genericTarget (algebraMap F (RatFunc F) x) =
        algebraMap F (RatFunc F) (target₀ x) +
          (RatFunc.X : RatFunc F) *
            algebraMap F (RatFunc F) (target₁ x))
    (hkernels : ∀ w ∈ T,
      LinearMap.ker (lowStackRelationMap S source
        (fun x ↦ target₀ x + w * target₁ x) h) ≠ ⊥) :
    LinearMap.ker
        (lowStackRelationMap
          (S.image (algebraMap F (RatFunc F)))
          genericSource genericTarget h) ≠ ⊥ ∧
      LinearMap.ker (lowStackRelationMap S source target₀ h) ≠ ⊥ ∧
      LinearMap.ker (lowStackRelationMap S source target₁ h) ≠ ⊥ := by
  have hgeneric := lowStack_generic_kernel_of_many_affine_kernels
    S T source target₀ target₁ genericSource genericTarget h hcard
    hgenericSource hgenericTarget hkernels
  have hendpoints := lowStack_endpoint_kernels_of_many_affine_kernels
    S T source target₀ target₁ h hcard hkernels
  exact ⟨hgeneric, hendpoints⟩

/-- Many affine low-stack kernels now feed directly into the checked
gcd-aware scroll construction. -/
noncomputable def scrollAtom_of_many_affine_lowStack_kernels
    {F : Type} [Field F] [DecidableEq F] [DecidableEq (RatFunc F)]
    (S T : Finset F) (source target₀ target₁ : F → F)
    (genericSource genericTarget : RatFunc F → RatFunc F) (h : ℕ)
    (hTcard : h < T.card)
    (hScard : h ≤ S.card)
    (hsource : ∀ x ∈ S, source x ≠ 0)
    (hgenericSource : ∀ x ∈ S,
      genericSource (algebraMap F (RatFunc F) x) =
        algebraMap F (RatFunc F) (source x))
    (hgenericTarget : ∀ x ∈ S,
      genericTarget (algebraMap F (RatFunc F) x) =
        algebraMap F (RatFunc F) (target₀ x) +
          (RatFunc.X : RatFunc F) *
            algebraMap F (RatFunc F) (target₁ x))
    (hstrict : 3 * h < S.card)
    (hkernels : ∀ w ∈ T,
      LinearMap.ker (lowStackRelationMap S source
        (fun x ↦ target₀ x + w * target₁ x) h) ≠ ⊥) :
    DefectAwareScrollAtom S source target₀ target₁ h := by
  let hthree := lowStack_three_kernels_of_many_affine_kernels
    S T source target₀ target₁ genericSource genericTarget h hTcard
    hgenericSource hgenericTarget hkernels
  exact scrollAtom_of_lowStack_kernels
    S source target₀ target₁ genericSource genericTarget h
    hScard hsource hgenericSource hgenericTarget hstrict
    hthree.1 hthree.2.1 hthree.2.2

end ProximityPrize.SubmissionLower
