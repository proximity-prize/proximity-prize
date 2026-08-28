import ProximityPrize.SubmissionLower.BCHKSFrobeniusKernelReduction6400

/-!
# Defect-aware three-fraction scroll interpolation

This module joins the generic kernel relation over `F(W)` with the two
specialized relations over `F`.  The valid sets may each lose the roots of a
cancelled gcd; their three loss budgets add, while the matching degree drops
keep the strict `3 * h < |S|` root count intact.
-/

namespace ProximityPrize.SubmissionLower

open Polynomial

variable {F : Type} [Field F]

/-- Three compatible reduced kernel relations force the product-denominator
cross identity used by the scroll argument.

The generic relation lives over `F(W)`.  Its target is required to specialize
on the embedded source set to `target₀ + W * target₁`; no behavior away from
that finite set is used. -/
theorem reduced_kernel_relations_product_cross_identity
    [DecidableEq F] [DecidableEq (RatFunc F)]
    (S : Finset F) (source target₀ target₁ : F → F)
    (genericSource genericTarget : RatFunc F → RatFunc F) (h : ℕ)
    (r : ReducedKernelRelation
      (S.image (algebraMap F (RatFunc F)))
      genericSource genericTarget h)
    (r₀ : ReducedKernelRelation S source target₀ h)
    (r₁ : ReducedKernelRelation S source target₁ h)
    (hsource : ∀ x ∈ S, source x ≠ 0)
    (hgenericSource : ∀ x ∈ S,
      genericSource (algebraMap F (RatFunc F) x) =
        algebraMap F (RatFunc F) (source x))
    (hgenericTarget : ∀ x ∈ S,
      genericTarget (algebraMap F (RatFunc F) x) =
        algebraMap F (RatFunc F) (target₀ x) +
          (RatFunc.X : RatFunc F) *
            algebraMap F (RatFunc F) (target₁ x))
    (hstrict : 3 * h < S.card) :
    r.numerator *
        (r₀.denominator.map (algebraMap F (RatFunc F)) *
          r₁.denominator.map (algebraMap F (RatFunc F))) =
      r.denominator *
        (r₀.numerator.map (algebraMap F (RatFunc F)) *
            r₁.denominator.map (algebraMap F (RatFunc F)) +
          Polynomial.C (RatFunc.X : RatFunc F) *
            (r₁.numerator.map (algebraMap F (RatFunc F)) *
              r₀.denominator.map (algebraMap F (RatFunc F)))) := by
  classical
  let φ : F →+* RatFunc F := algebraMap F (RatFunc F)
  let Sg : Finset (RatFunc F) := S.image φ
  let T : Finset (RatFunc F) :=
    r.valid ∩ r₀.valid.image φ ∩ r₁.valid.image φ
  have hφ : Function.Injective φ := φ.injective
  have hSgcard : Sg.card = S.card := by
    exact Finset.card_image_of_injective S hφ
  have hT₀subset : r₀.valid.image φ ⊆ Sg :=
    Finset.image_mono φ r₀.valid_subset
  have hT₁subset : r₁.valid.image φ ⊆ Sg :=
    Finset.image_mono φ r₁.valid_subset
  have hT₀coverage :
      Sg.card ≤ (r₀.valid.image φ).card + r₀.removedGcd.natDegree := by
    rw [hSgcard, Finset.card_image_of_injective r₀.valid hφ]
    exact r₀.coverage
  have hT₁coverage :
      Sg.card ≤ (r₁.valid.image φ).card + r₁.removedGcd.natDegree := by
    rw [hSgcard, Finset.card_image_of_injective r₁.valid hφ]
    exact r₁.coverage
  have hcoverage :
      Sg.card ≤ T.card +
        (r.removedGcd.natDegree + r₀.removedGcd.natDegree +
          r₁.removedGcd.natDegree) := by
    exact card_triple_intersection_with_defects
      Sg r.valid (r₀.valid.image φ) (r₁.valid.image φ)
      r.removedGcd.natDegree r₀.removedGcd.natDegree
      r₁.removedGcd.natDegree r.valid_subset hT₀subset hT₁subset
      r.coverage hT₀coverage hT₁coverage
  have hstrictGeneric : 3 * h < Sg.card := by
    simpa only [hSgcard] using hstrict
  have heval : ∀ y ∈ T,
      r.numerator.eval y * (r₀.denominator.map φ).eval y *
          (r₁.denominator.map φ).eval y =
        r.denominator.eval y *
          ((r₀.numerator.map φ).eval y *
              (r₁.denominator.map φ).eval y +
            (RatFunc.X : RatFunc F) *
              ((r₁.numerator.map φ).eval y *
                (r₀.denominator.map φ).eval y)) := by
    intro y hy
    rcases Finset.mem_inter.mp hy with ⟨hyr₀, hyr₁⟩
    rcases Finset.mem_inter.mp hyr₀ with ⟨hyr, hy₀⟩
    rcases Finset.mem_image.mp hy₀ with ⟨x, hx₀, rfl⟩
    rcases Finset.mem_image.mp hyr₁ with ⟨x₁, hx₁, hx₁eq⟩
    have hx₁x : x₁ = x := hφ hx₁eq
    subst x₁
    have hxS : x ∈ S := r₀.valid_subset hx₀
    have hgeneric := r.interpolation (φ x) hyr
    rw [hgenericSource x hxS, hgenericTarget x hxS] at hgeneric
    have hzero : φ (source x) ≠ 0 :=
      (_root_.map_ne_zero φ).2 (hsource x hxS)
    have h₀ :
        (r₀.numerator.map φ).eval (φ x) * φ (source x) =
          (r₀.denominator.map φ).eval (φ x) * φ (target₀ x) := by
      simpa only [Polynomial.eval_map, Polynomial.eval₂_at_apply, map_mul]
        using congrArg φ (r₀.interpolation x hx₀)
    have h₁ :
        (r₁.numerator.map φ).eval (φ x) * φ (source x) =
          (r₁.denominator.map φ).eval (φ x) * φ (target₁ x) := by
      simpa only [Polynomial.eval_map, Polynomial.eval₂_at_apply, map_mul]
        using congrArg φ (r₁.interpolation x hx₁)
    apply mul_right_cancel₀ hzero
    calc
      (r.numerator.eval (φ x) * (r₀.denominator.map φ).eval (φ x) *
          (r₁.denominator.map φ).eval (φ x)) * φ (source x) =
          (r.numerator.eval (φ x) * φ (source x)) *
            (r₀.denominator.map φ).eval (φ x) *
              (r₁.denominator.map φ).eval (φ x) := by ring
      _ = (r.denominator.eval (φ x) *
            (φ (target₀ x) + (RatFunc.X : RatFunc F) * φ (target₁ x))) *
            (r₀.denominator.map φ).eval (φ x) *
              (r₁.denominator.map φ).eval (φ x) := by rw [hgeneric]
      _ = r.denominator.eval (φ x) *
          (((r₀.denominator.map φ).eval (φ x) * φ (target₀ x)) *
              (r₁.denominator.map φ).eval (φ x) +
            (RatFunc.X : RatFunc F) *
              (((r₁.denominator.map φ).eval (φ x) * φ (target₁ x)) *
                (r₀.denominator.map φ).eval (φ x))) := by ring
      _ = r.denominator.eval (φ x) *
          (((r₀.numerator.map φ).eval (φ x) * φ (source x)) *
              (r₁.denominator.map φ).eval (φ x) +
            (RatFunc.X : RatFunc F) *
              (((r₁.numerator.map φ).eval (φ x) * φ (source x)) *
                (r₀.denominator.map φ).eval (φ x))) := by rw [h₀, h₁]
      _ = (r.denominator.eval (φ x) *
          ((r₀.numerator.map φ).eval (φ x) *
              (r₁.denominator.map φ).eval (φ x) +
            (RatFunc.X : RatFunc F) *
              ((r₁.numerator.map φ).eval (φ x) *
                (r₀.denominator.map φ).eval (φ x)))) * φ (source x) := by ring
  have hcross :
      r.numerator * (r₀.denominator.map φ) * (r₁.denominator.map φ) =
        r.denominator *
          ((r₀.numerator.map φ) * (r₁.denominator.map φ) +
            Polynomial.C (RatFunc.X : RatFunc F) *
              ((r₁.numerator.map φ) * (r₀.denominator.map φ))) := by
    apply generic_interpolant_cross_identity_with_defects
      r.numerator r.denominator
      (r₀.numerator.map φ) (r₀.denominator.map φ)
      (r₁.numerator.map φ) (r₁.denominator.map φ)
      (RatFunc.X : RatFunc F) Sg T h
      r.removedGcd.natDegree r₀.removedGcd.natDegree
      r₁.removedGcd.natDegree
    · exact r.numerator_degree
    · exact r.denominator_degree
    · simpa only [Polynomial.natDegree_map_eq_of_injective hφ] using
        r₀.numerator_degree
    · simpa only [Polynomial.natDegree_map_eq_of_injective hφ] using
        r₀.denominator_degree
    · simpa only [Polynomial.natDegree_map_eq_of_injective hφ] using
        r₁.numerator_degree
    · simpa only [Polynomial.natDegree_map_eq_of_injective hφ] using
        r₁.denominator_degree
    · exact hstrictGeneric
    · exact hcoverage
    · exact heval
  simpa only [mul_assoc] using hcross

/-- Degree-only consequence of the three-relation product identity. -/
theorem reduced_kernel_relations_scroll_degree_transfer
    [DecidableEq F] [DecidableEq (RatFunc F)]
    (S : Finset F) (source target₀ target₁ : F → F)
    (genericSource genericTarget : RatFunc F → RatFunc F) (h : ℕ)
    (r : ReducedKernelRelation
      (S.image (algebraMap F (RatFunc F)))
      genericSource genericTarget h)
    (r₀ : ReducedKernelRelation S source target₀ h)
    (r₁ : ReducedKernelRelation S source target₁ h)
    (hsource : ∀ x ∈ S, source x ≠ 0)
    (hgenericSource : ∀ x ∈ S,
      genericSource (algebraMap F (RatFunc F) x) =
        algebraMap F (RatFunc F) (source x))
    (hgenericTarget : ∀ x ∈ S,
      genericTarget (algebraMap F (RatFunc F) x) =
        algebraMap F (RatFunc F) (target₀ x) +
          (RatFunc.X : RatFunc F) *
            algebraMap F (RatFunc F) (target₁ x))
    (hstrict : 3 * h < S.card) :
    (lcm r₀.denominator r₁.denominator).natDegree < h ∧
      (r₀.numerator *
        (lcm r₀.denominator r₁.denominator / r₀.denominator)).natDegree < h ∧
      (r₁.numerator *
        (lcm r₀.denominator r₁.denominator / r₁.denominator)).natDegree < h := by
  have hcross := reduced_kernel_relations_product_cross_identity
    S source target₀ target₁ genericSource genericTarget h r r₀ r₁
    hsource hgenericSource hgenericTarget hstrict
  apply lcm_adjusted_fraction_degree_transfer_of_product_cross_identity
    r₀.numerator r₀.denominator r₁.numerator r₁.denominator
    r.numerator r.denominator h
    r₀.denominator_ne_zero r₁.denominator_ne_zero r.denominator_ne_zero
    r₀.reduced r₁.reduced
  · have hdegree := r.numerator_degree
    omega
  · have hdegree := r.denominator_degree
    omega
  · exact hcross

/-- A common-denominator scroll atom whose single loss budget is paid by the
degree removed from the generic kernel relation. -/
structure DefectAwareScrollAtom
    (S : Finset F) (source target₀ target₁ : F → F) (h : ℕ) where
  numerator₀ : F[X]
  numerator₁ : F[X]
  denominator : F[X]
  loss : ℕ
  valid : Finset F
  denominator_ne_zero : denominator ≠ 0
  numerator₀_degree : numerator₀.natDegree + loss < h
  numerator₁_degree : numerator₁.natDegree + loss < h
  denominator_degree : denominator.natDegree + loss < h
  valid_subset : valid ⊆ S
  coverage : S.card ≤ valid.card + loss
  interpolation₀ : ∀ x ∈ valid,
    numerator₀.eval x * source x = denominator.eval x * target₀ x
  interpolation₁ : ∀ x ∈ valid,
    numerator₁.eval x * source x = denominator.eval x * target₁ x

/-- Assemble a defect-aware scroll atom.

Although all three reduced relations are used to prove the global cross
identity, the final base relations propagate to every point where the
*generic* reduced relation is valid.  Coprimality makes its denominator
nonzero there, and coefficient separation in `F(W)` recovers the two base
relations.  Consequently only the generic gcd contributes to `loss`. -/
noncomputable def reduced_kernel_relations_scroll_atom
    [DecidableEq F] [DecidableEq (RatFunc F)]
    (S : Finset F) (source target₀ target₁ : F → F)
    (genericSource genericTarget : RatFunc F → RatFunc F) (h : ℕ)
    (r : ReducedKernelRelation
      (S.image (algebraMap F (RatFunc F)))
      genericSource genericTarget h)
    (r₀ : ReducedKernelRelation S source target₀ h)
    (r₁ : ReducedKernelRelation S source target₁ h)
    (hsource : ∀ x ∈ S, source x ≠ 0)
    (hgenericSource : ∀ x ∈ S,
      genericSource (algebraMap F (RatFunc F) x) =
        algebraMap F (RatFunc F) (source x))
    (hgenericTarget : ∀ x ∈ S,
      genericTarget (algebraMap F (RatFunc F) x) =
        algebraMap F (RatFunc F) (target₀ x) +
          (RatFunc.X : RatFunc F) *
            algebraMap F (RatFunc F) (target₁ x))
    (hstrict : 3 * h < S.card) :
    DefectAwareScrollAtom S source target₀ target₁ h := by
  classical
  let φ : F →+* RatFunc F := algebraMap F (RatFunc F)
  let L : F[X] := lcm r₀.denominator r₁.denominator
  let A₀ : F[X] := r₀.numerator * (L / r₀.denominator)
  let A₁ : F[X] := r₁.numerator * (L / r₁.denominator)
  let T : Finset F := S.filter (fun x ↦ φ x ∈ r.valid)
  have hφ : Function.Injective φ := φ.injective
  have hLne : L ≠ 0 := by
    dsimp only [L]
    rw [Ne, lcm_eq_zero_iff]
    exact not_or_intro r₀.denominator_ne_zero r₁.denominator_ne_zero
  have hcrossProduct := reduced_kernel_relations_product_cross_identity
    S source target₀ target₁ genericSource genericTarget h r r₀ r₁
    hsource hgenericSource hgenericTarget hstrict
  have hcross :
      r.numerator * L.map φ =
        (A₀.map φ + (RatFunc.X : RatFunc F) • A₁.map φ) *
          r.denominator := by
    exact lcm_cross_identity_of_product_cross_identity
      r₀.numerator r₀.denominator r₁.numerator r₁.denominator
      r.numerator r.denominator r₀.denominator_ne_zero
      r₁.denominator_ne_zero hcrossProduct
  have hdegree :=
    lcm_adjusted_fraction_degree_transfer_le_of_product_cross_identity
      r₀.numerator r₀.denominator r₁.numerator r₁.denominator
      r.numerator r.denominator r₀.denominator_ne_zero
      r₁.denominator_ne_zero r.denominator_ne_zero r₀.reduced r₁.reduced
      hcrossProduct
  have hLdegree : L.natDegree + r.removedGcd.natDegree < h := by
    have hrdegree := r.denominator_degree
    dsimp only [L]
    omega
  have hA₀degree : A₀.natDegree + r.removedGcd.natDegree < h := by
    have hrdegree := r.numerator_degree
    dsimp only [A₀, L]
    omega
  have hA₁degree : A₁.natDegree + r.removedGcd.natDegree < h := by
    have hrdegree := r.numerator_degree
    dsimp only [A₁, L]
    omega
  have hTsubset : T ⊆ S := by
    intro x hx
    exact (Finset.mem_filter.mp hx).1
  have hTimage : T.image φ = r.valid := by
    ext y
    constructor
    · intro hy
      rcases Finset.mem_image.mp hy with ⟨x, hx, hxy⟩
      have hxvalid := (Finset.mem_filter.mp hx).2
      rw [hxy] at hxvalid
      exact hxvalid
    · intro hy
      have hyS := r.valid_subset hy
      rcases Finset.mem_image.mp hyS with ⟨x, hxS, hxy⟩
      apply Finset.mem_image.mpr
      refine ⟨x, Finset.mem_filter.mpr ⟨hxS, ?_⟩, hxy⟩
      rw [hxy]
      exact hy
  have hTcard : T.card = r.valid.card := by
    have himage := Finset.card_image_of_injective T hφ
    rw [hTimage] at himage
    exact himage.symm
  have hSimagecard : (S.image φ).card = S.card :=
    Finset.card_image_of_injective S hφ
  have hcoverage : S.card ≤ T.card + r.removedGcd.natDegree := by
    have hrcoverage := r.coverage
    rw [hSimagecard, ← hTcard] at hrcoverage
    exact hrcoverage
  have hrelations : ∀ x ∈ T,
      A₀.eval x * source x = L.eval x * target₀ x ∧
        A₁.eval x * source x = L.eval x * target₁ x := by
    intro x hx
    have hxS := (Finset.mem_filter.mp hx).1
    have hxvalid := (Finset.mem_filter.mp hx).2
    have hgeneric := r.interpolation (φ x) hxvalid
    rw [hgenericSource x hxS, hgenericTarget x hxS] at hgeneric
    have hsourceMap : φ (source x) ≠ 0 :=
      (_root_.map_ne_zero φ).2 (hsource x hxS)
    have hdenominatorPoint : r.denominator.eval (φ x) ≠ 0 := by
      intro hDzero
      have hNproduct : r.numerator.eval (φ x) * φ (source x) = 0 := by
        rw [hgeneric, hDzero, zero_mul]
      have hNzero : r.numerator.eval (φ x) = 0 :=
        (mul_eq_zero.mp hNproduct).resolve_right hsourceMap
      rcases r.reduced with ⟨U, V, hbezout⟩
      have hevalBezout := congrArg
        (fun P : (RatFunc F)[X] ↦ P.eval (φ x)) hbezout
      simp only [Polynomial.eval_add, Polynomial.eval_mul,
        Polynomial.eval_one, hNzero, hDzero, mul_zero, add_zero] at hevalBezout
      exact zero_ne_one hevalBezout
    have hcrossEval := congrArg
      (fun P : (RatFunc F)[X] ↦ P.eval (φ x)) hcross
    simp only [Polynomial.eval_mul, Polynomial.eval_add,
      Polynomial.eval_map, Polynomial.eval₂_at_apply,
      Polynomial.eval_smul, smul_eq_mul] at hcrossEval
    have hcombination :
        (φ (A₀.eval x) + (RatFunc.X : RatFunc F) * φ (A₁.eval x)) *
            φ (source x) =
          φ (L.eval x) *
            (φ (target₀ x) +
              (RatFunc.X : RatFunc F) * φ (target₁ x)) := by
      apply mul_right_cancel₀ hdenominatorPoint
      calc
        ((φ (A₀.eval x) + (RatFunc.X : RatFunc F) * φ (A₁.eval x)) *
            φ (source x)) * r.denominator.eval (φ x) =
            (r.numerator.eval (φ x) * φ (L.eval x)) *
              φ (source x) := by rw [hcrossEval]; ring
        _ = φ (L.eval x) *
              (r.numerator.eval (φ x) * φ (source x)) := by ring
        _ = φ (L.eval x) *
              (r.denominator.eval (φ x) *
                (φ (target₀ x) +
                  (RatFunc.X : RatFunc F) * φ (target₁ x))) := by
            rw [hgeneric]
        _ = (φ (L.eval x) *
              (φ (target₀ x) +
                (RatFunc.X : RatFunc F) * φ (target₁ x))) *
              r.denominator.eval (φ x) := by ring
    have hlinear :
        φ (A₀.eval x * source x - L.eval x * target₀ x) +
            (RatFunc.X : RatFunc F) *
              φ (A₁.eval x * source x - L.eval x * target₁ x) = 0 := by
      simp only [map_sub, map_mul]
      calc
        (φ (A₀.eval x) * φ (source x) -
              φ (L.eval x) * φ (target₀ x)) +
            (RatFunc.X : RatFunc F) *
              (φ (A₁.eval x) * φ (source x) -
                φ (L.eval x) * φ (target₁ x)) =
            (φ (A₀.eval x) +
                (RatFunc.X : RatFunc F) * φ (A₁.eval x)) *
              φ (source x) -
              φ (L.eval x) *
                (φ (target₀ x) +
                  (RatFunc.X : RatFunc F) * φ (target₁ x)) := by ring
        _ = 0 := sub_eq_zero.mpr hcombination
    have hcoefficients :=
      (ratFunc_linear_eq_zero_iff
        (A₀.eval x * source x - L.eval x * target₀ x)
        (A₁.eval x * source x - L.eval x * target₁ x)).mp hlinear
    exact ⟨sub_eq_zero.mp hcoefficients.1,
      sub_eq_zero.mp hcoefficients.2⟩
  exact
    { numerator₀ := A₀
      numerator₁ := A₁
      denominator := L
      loss := r.removedGcd.natDegree
      valid := T
      denominator_ne_zero := hLne
      numerator₀_degree := hA₀degree
      numerator₁_degree := hA₁degree
      denominator_degree := hLdegree
      valid_subset := hTsubset
      coverage := hcoverage
      interpolation₀ := fun x hx ↦ (hrelations x hx).1
      interpolation₁ := fun x hx ↦ (hrelations x hx).2 }

end ProximityPrize.SubmissionLower
