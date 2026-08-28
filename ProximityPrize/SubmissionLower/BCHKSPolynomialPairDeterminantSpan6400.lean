import ProximityPrize.SubmissionLower.BCHKSPolynomialPairDeterminant6400

/-!
# Bilinear span of polynomial-pair determinants

This module proves that taking the alternating determinant after passing to
the span of a finite family creates no new linear directions: every such
determinant lies in the span of the original pairwise determinants.  This is
the finite-family bridge needed by the locator rank-drop/Cramer argument.
-/

namespace ProximityPrize.SubmissionLower

open Polynomial

set_option autoImplicit false

variable {F : Type} [Field F]

@[simp]
theorem polynomialPairDet_zero_left {c h : ℕ}
    (v : PolynomialPairSpace F c h) :
    polynomialPairDet (0 : PolynomialPairSpace F c h) v = 0 := by
  simp [polynomialPairDet]

@[simp]
theorem polynomialPairDet_add_left {c h : ℕ}
    (u v w : PolynomialPairSpace F c h) :
    polynomialPairDet (u + v) w =
      polynomialPairDet u w + polynomialPairDet v w := by
  simp only [polynomialPairDet, Prod.fst_add, Prod.snd_add,
    Submodule.coe_add]
  ring

@[simp]
theorem polynomialPairDet_smul_left {c h : ℕ}
    (a : F) (u v : PolynomialPairSpace F c h) :
    polynomialPairDet (a • u) v = a • polynomialPairDet u v := by
  simp only [polynomialPairDet, Prod.smul_fst, Prod.smul_snd,
    Submodule.coe_smul_of_tower, smul_eq_C_mul]
  ring

@[simp]
theorem polynomialPairDet_zero_right {c h : ℕ}
    (u : PolynomialPairSpace F c h) :
    polynomialPairDet u (0 : PolynomialPairSpace F c h) = 0 := by
  simp [polynomialPairDet]

@[simp]
theorem polynomialPairDet_add_right {c h : ℕ}
    (u v w : PolynomialPairSpace F c h) :
    polynomialPairDet u (v + w) =
      polynomialPairDet u v + polynomialPairDet u w := by
  simpa only [polynomialPairDetLinear_apply] using
    (polynomialPairDetLinear u).map_add v w

@[simp]
theorem polynomialPairDet_smul_right {c h : ℕ}
    (a : F) (u v : PolynomialPairSpace F c h) :
    polynomialPairDet u (a • v) = a • polynomialPairDet u v := by
  simpa only [polynomialPairDetLinear_apply] using
    (polynomialPairDetLinear u).map_smul a v

/-- Determinants of two vectors in a finite span lie in the span of the
pairwise determinants of the original family. -/
theorem polynomialPairDet_mem_span_pairwise
    {I : Type} [Fintype I] {c h : ℕ}
    (family : I → PolynomialPairSpace F c h)
    (u v : PolynomialPairSpace F c h)
    (hu : u ∈ Submodule.span F (Set.range family))
    (hv : v ∈ Submodule.span F (Set.range family)) :
    polynomialPairDet u v ∈
      Submodule.span F (Set.range
        (fun ij : I × I => polynomialPairDet (family ij.1) (family ij.2))) := by
  let C : Submodule F F[X] := Submodule.span F (Set.range
    (fun ij : I × I => polynomialPairDet (family ij.1) (family ij.2)))
  have hgenerator (i : I) : ∀ w,
      w ∈ Submodule.span F (Set.range family) →
      polynomialPairDet (family i) w ∈ C := by
    intro w hw
    refine Submodule.span_induction (p := fun y _ =>
      polynomialPairDet (family i) y ∈ C) ?_ ?_ ?_ ?_ hw
    · intro y hy
      rcases hy with ⟨j, rfl⟩
      exact Submodule.subset_span ⟨(i, j), rfl⟩
    · simpa using C.zero_mem
    · intro y z hy hz hdy hdz
      simpa using C.add_mem hdy hdz
    · intro a y hy hdy
      simpa using C.smul_mem a hdy
  refine Submodule.span_induction (p := fun x _ =>
    polynomialPairDet x v ∈ C) ?_ ?_ ?_ ?_ hu
  · intro x hx
    rcases hx with ⟨i, rfl⟩
    exact hgenerator i v hv
  · simpa using C.zero_mem
  · intro x y hx hy hdx hdy
    simpa using C.add_mem hdx hdy
  · intro a x hx hdx
    simpa using C.smul_mem a hdx

end ProximityPrize.SubmissionLower
