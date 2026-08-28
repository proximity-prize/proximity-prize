import ProximityPrize.SubmissionLower.BCHKSFrobeniusGenericPencil6400

/-!
# Gcd-aware reduction of a source-kernel relation

A low-stack kernel relation supplies two bounded polynomials.  Dividing their
gcd produces a reduced rational interpolant, but can discard source points at
roots of that gcd.  This module packages the exact degree/cardinality trade:
the removed gcd lowers both degrees by its degree and erases at most that many
source coordinates.
-/

namespace ProximityPrize.SubmissionLower

open Polynomial

variable {F : Type} [Field F]

/-- A reduced rational interpolation relation together with the exact budget
for source coordinates lost while cancelling its gcd. -/
structure ReducedKernelRelation
    (S : Finset F) (source target : F → F) (h : ℕ) where
  numerator : F[X]
  denominator : F[X]
  removedGcd : F[X]
  valid : Finset F
  removedGcd_ne_zero : removedGcd ≠ 0
  denominator_ne_zero : denominator ≠ 0
  numerator_degree : numerator.natDegree + removedGcd.natDegree < h
  denominator_degree : denominator.natDegree + removedGcd.natDegree < h
  reduced : IsCoprime numerator denominator
  valid_subset : valid ⊆ S
  coverage : S.card ≤ valid.card + removedGcd.natDegree
  interpolation : ∀ x ∈ valid,
    numerator.eval x * source x = denominator.eval x * target x

/-- The losses from intersecting three valid subsets add. -/
theorem card_triple_intersection_with_defects
    {I : Type} [DecidableEq I]
    (S T T₀ T₁ : Finset I) (g g₀ g₁ : ℕ)
    (hT : T ⊆ S) (hT₀ : T₀ ⊆ S) (hT₁ : T₁ ⊆ S)
    (hcover : S.card ≤ T.card + g)
    (hcover₀ : S.card ≤ T₀.card + g₀)
    (hcover₁ : S.card ≤ T₁.card + g₁) :
    S.card ≤ (T ∩ T₀ ∩ T₁).card + (g + g₀ + g₁) := by
  have hbad (U : Finset I) (d : ℕ) (hU : U ⊆ S)
      (hUcover : S.card ≤ U.card + d) :
      (S \ U).card ≤ d := by
    have hpartition := Finset.card_sdiff_add_card_eq_card hU
    omega
  have hbadT := hbad T g hT hcover
  have hbadT₀ := hbad T₀ g₀ hT₀ hcover₀
  have hbadT₁ := hbad T₁ g₁ hT₁ hcover₁
  have hcommonSubset : T ∩ T₀ ∩ T₁ ⊆ S := by
    intro x hx
    exact hT (Finset.mem_inter.mp (Finset.mem_inter.mp hx).1).1
  have hdiff : S \ (T ∩ T₀ ∩ T₁) =
      (S \ T) ∪ (S \ T₀) ∪ (S \ T₁) := by
    ext x
    simp only [Finset.mem_sdiff, Finset.mem_inter, Finset.mem_union]
    tauto
  have hbadCommon : (S \ (T ∩ T₀ ∩ T₁)).card ≤
      g + g₀ + g₁ := by
    rw [hdiff]
    calc
      ((S \ T) ∪ (S \ T₀) ∪ (S \ T₁)).card ≤
          ((S \ T) ∪ (S \ T₀)).card + (S \ T₁).card :=
        Finset.card_union_le _ _
      _ ≤ ((S \ T).card + (S \ T₀).card) + (S \ T₁).card := by
        exact Nat.add_le_add_right (Finset.card_union_le _ _) _
      _ ≤ g + g₀ + g₁ := by omega
  have hpartition := Finset.card_sdiff_add_card_eq_card hcommonSubset
  omega

/-- Divide a nontrivial bounded kernel relation by its polynomial gcd.

The source multiplier must be nonzero on `S`; this forces the second kernel
polynomial to be nonzero, since otherwise the first would have at least
`h` roots despite degree `<h`.  The reduced relation is asserted only away
from roots of the cancelled gcd, and `coverage` bounds the lost coordinates.
-/
noncomputable def reducedKernelRelation_of_polynomial_relation
    [DecidableEq F]
    (A B : F[X]) (S : Finset F) (source target : F → F) (h : ℕ)
    (hnontrivial : ¬(A = 0 ∧ B = 0))
    (hAdegree : A.natDegree < h) (hBdegree : B.natDegree < h)
    (hcard : h ≤ S.card)
    (hsource : ∀ x ∈ S, source x ≠ 0)
    (hrelation : ∀ x ∈ S,
      A.eval x * source x + B.eval x * target x = 0) :
    ReducedKernelRelation S source target h := by
  classical
  have hBne : B ≠ 0 := by
    intro hBzero
    have hAroot : ∀ x ∈ S, A.eval x = 0 := by
      intro x hx
      have hzero : A.eval x * source x = 0 := by
        simpa [hBzero] using hrelation x hx
      exact (mul_eq_zero.mp hzero).resolve_right (hsource x hx)
    have hAzero : A = 0 :=
      Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero'
        A S hAroot (hAdegree.trans_le hcard)
    exact hnontrivial ⟨hAzero, hBzero⟩
  let G : F[X] := gcd A B
  let N : F[X] := -(A / G)
  let D : F[X] := B / G
  let T : Finset F := S.filter (fun x ↦ G.eval x ≠ 0)
  have hGne : G ≠ 0 := by
    intro hGzero
    have hz := (gcd_eq_zero_iff A B).mp hGzero
    exact hnontrivial hz
  have hGdvdA : G ∣ A := GCDMonoid.gcd_dvd_left A B
  have hGdvdB : G ∣ B := GCDMonoid.gcd_dvd_right A B
  have hDne : D ≠ 0 := by
    exact right_div_gcd_ne_zero hBne
  have hBfactor : G * D = B := by
    exact EuclideanDomain.mul_div_cancel' hGne hGdvdB
  have hDdegree : D.natDegree + G.natDegree < h := by
    have hdegree : G.natDegree + D.natDegree = B.natDegree := by
      calc
        G.natDegree + D.natDegree = (G * D).natDegree :=
          (Polynomial.natDegree_mul hGne hDne).symm
        _ = B.natDegree := congrArg Polynomial.natDegree hBfactor
    omega
  have hNdegree : N.natDegree + G.natDegree < h := by
    by_cases hAne : A ≠ 0
    · have hAdivne : A / G ≠ 0 := left_div_gcd_ne_zero hAne
      have hAfactor : G * (A / G) = A :=
        EuclideanDomain.mul_div_cancel' hGne hGdvdA
      have hdegree : G.natDegree + (A / G).natDegree = A.natDegree := by
        calc
          G.natDegree + (A / G).natDegree = (G * (A / G)).natDegree :=
            (Polynomial.natDegree_mul hGne hAdivne).symm
          _ = A.natDegree := congrArg Polynomial.natDegree hAfactor
      dsimp only [N]
      rw [Polynomial.natDegree_neg]
      omega
    · have hAzero : A = 0 := not_ne_iff.mp hAne
      have hGdegree : G.natDegree ≤ B.natDegree :=
        Polynomial.natDegree_le_of_dvd hGdvdB hBne
      dsimp only [N]
      simp only [hAzero, EuclideanDomain.zero_div, neg_zero,
        Polynomial.natDegree_zero, zero_add]
      exact hGdegree.trans_lt hBdegree
  have hreduced : IsCoprime N D := by
    exact (isCoprime_div_gcd_div_gcd hBne).neg_left
  have hTsubset : T ⊆ S := by
    intro x hx
    exact (Finset.mem_filter.mp hx).1
  have hbad :
      (S.filter (fun x ↦ G.eval x = 0)).card ≤ G.natDegree := by
    have hsubset : S.filter (fun x ↦ G.eval x = 0) ⊆ G.roots.toFinset := by
      intro x hx
      have hxzero := (Finset.mem_filter.mp hx).2
      rw [Multiset.mem_toFinset, Polynomial.mem_roots hGne]
      exact hxzero
    calc
      (S.filter (fun x ↦ G.eval x = 0)).card ≤ G.roots.toFinset.card :=
        Finset.card_le_card hsubset
      _ ≤ G.roots.card := Multiset.toFinset_card_le _
      _ ≤ G.natDegree := Polynomial.card_roots' G
  have hcoverage : S.card ≤ T.card + G.natDegree := by
    have hpartition := Finset.card_filter_add_card_filter_not
      (fun x ↦ G.eval x ≠ 0) (s := S)
    change T.card + (S.filter (fun x ↦ ¬G.eval x ≠ 0)).card = S.card at hpartition
    have hbad' : (S.filter (fun x ↦ ¬G.eval x ≠ 0)).card ≤
        G.natDegree := by
      simpa only [not_ne_iff] using hbad
    omega
  have hinterpolation : ∀ x ∈ T,
      N.eval x * source x = D.eval x * target x := by
    intro x hx
    have hxparts := Finset.mem_filter.mp hx
    have hxS : x ∈ S := hxparts.1
    have hxG : G.eval x ≠ 0 := hxparts.2
    have hAfactor : G * (A / G) = A :=
      EuclideanDomain.mul_div_cancel' hGne hGdvdA
    have hfull := hrelation x hxS
    rw [← hAfactor, ← hBfactor,
      Polynomial.eval_mul, Polynomial.eval_mul] at hfull
    have hfactored : G.eval x *
        ((A / G).eval x * source x + D.eval x * target x) = 0 := by
      linear_combination hfull
    have hinside :
        (A / G).eval x * source x + D.eval x * target x = 0 :=
      (mul_eq_zero.mp hfactored).resolve_left hxG
    dsimp only [N]
    rw [Polynomial.eval_neg]
    linear_combination -hinside
  exact
    { numerator := N
      denominator := D
      removedGcd := G
      valid := T
      removedGcd_ne_zero := hGne
      denominator_ne_zero := hDne
      numerator_degree := hNdegree
      denominator_degree := hDdegree
      reduced := hreduced
      valid_subset := hTsubset
      coverage := hcoverage
      interpolation := hinterpolation }

end ProximityPrize.SubmissionLower
