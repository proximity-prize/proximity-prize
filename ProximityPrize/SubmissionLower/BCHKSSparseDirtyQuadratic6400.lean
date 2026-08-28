import ProximityPrize.SubmissionLower.BCHKSDoubleCounting

/-!
# Sparse dirty-coordinate alignment for the score-64 route

This file isolates the two algebraic/combinatorial facts needed by the
high-identity, nonsimple-coordinate branch.  No benchmark claim is changed
here.
-/

namespace ProximityPrize.SubmissionLower

open Polynomial
open scoped BigOperators

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

/-- The high-identity branch contains the exact number of nonsimple
coordinates needed by the sparse-dirty argument. -/
theorem exists_sparse_nonsimple_coordinates_6400
    {ι : Type} [DecidableEq ι] (I Simple : Finset ι)
    (hSimple : Simple ⊆ I)
    (hI : 262066 ≤ I.card)
    (hSimpleCard : Simple.card ≤ 130653) :
  ∃ W ⊆ I \ Simple, W.card = 131413 := by
  have hcard : 131413 ≤ (I \ Simple).card := by
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hSimple]
    omega
  exact Finset.exists_subset_card_eq hcard

/-- Sharp dichotomy furnished by the weighted fixed-factor incidence count.
Among `185331` identity coordinates, either the simple locus already has
`53919` points, or the nonsimple locus contains the `131413` coordinates
needed by the sparse-dirty interpolation argument. -/
theorem large_simple_or_exists_sparse_nonsimple_coordinates_6400
    {ι : Type} [DecidableEq ι] (I Simple : Finset ι)
    (hSimple : Simple ⊆ I)
    (hI : 185331 ≤ I.card) :
    53919 ≤ Simple.card ∨
      ∃ W ⊆ I \ Simple, W.card = 131413 := by
  by_cases hlarge : 53919 ≤ Simple.card
  · exact Or.inl hlarge
  · right
    have hSimpleCard : Simple.card ≤ 53918 := by omega
    have hcard : 131413 ≤ (I \ Simple).card := by
      rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hSimple]
      omega
    exact Finset.exists_subset_card_eq hcard

/-- Stronger score-64 dichotomy after the adaptive sparse-row argument has
excluded every identity locus of size at most `212478`. -/
theorem large_simple_or_exists_sparse_nonsimple_coordinates_extended_6400
    {ι : Type} [DecidableEq ι] (I Simple : Finset ι)
    (hSimple : Simple ⊆ I)
    (hI : 212479 ≤ I.card) :
    81067 ≤ Simple.card ∨
      ∃ W ⊆ I \ Simple, W.card = 131413 := by
  by_cases hlarge : 81067 ≤ Simple.card
  · exact Or.inl hlarge
  · right
    have hSimpleCard : Simple.card ≤ 81066 := by omega
    have hcard : 131413 ≤ (I \ Simple).card := by
      rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hSimple]
      omega
    exact Finset.exists_subset_card_eq hcard

variable {F : Type} [Field F]

/-- A quadratic polynomial section with a repeated generic root has no other
root after a specialization which preserves its quadratic coefficient. -/
theorem quadratic_specialized_root_unique
    (B : F[X][X]) (L : F[X]) (z y : F)
    (hdeg : B.natDegree ≤ 2)
    (hroot : B.eval L = 0)
    (hderiv : B.derivative.eval L = 0)
    (hquad : (B.coeff 2).eval z ≠ 0)
    (hy : (B.map (Polynomial.evalRingHom z)).eval y = 0) :
    y = L.eval z := by
  have hshape : B =
      Polynomial.C (B.coeff 0) +
        Polynomial.C (B.coeff 1) * Polynomial.X +
          Polynomial.C (B.coeff 2) * Polynomial.X ^ 2 := by
    ext n
    rcases n with _ | n
    · simp
    rcases n with _ | n
    · simp
    rcases n with _ | n
    · simp
    · have hn : B.natDegree < n.succ.succ.succ := by omega
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt hn]
      simp
  have hrootz :
      (B.coeff 0).eval z + (B.coeff 1).eval z * L.eval z +
          (B.coeff 2).eval z * (L.eval z) ^ 2 = 0 := by
    rw [hshape] at hroot
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X, Polynomial.eval_pow] at hroot
    have hz := congrArg (Polynomial.eval z) hroot
    simpa only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_zero] using hz
  have hderivz :
      (B.coeff 1).eval z + 2 * (B.coeff 2).eval z * L.eval z = 0 := by
    rw [hshape] at hderiv
    simp only [Polynomial.derivative_add, Polynomial.derivative_mul,
      Polynomial.derivative_C, Polynomial.derivative_X,
      Polynomial.derivative_pow, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_pow, zero_mul,
      zero_add, mul_one] at hderiv
    have hz := congrArg (Polynomial.eval z) hderiv
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_zero] at hz
    norm_num [Polynomial.eval_natCast] at hz
    simpa only [mul_assoc, mul_left_comm, mul_comm] using hz
  have hy' :
      (B.coeff 0).eval z + (B.coeff 1).eval z * y +
          (B.coeff 2).eval z * y ^ 2 = 0 := by
    rw [hshape, Polynomial.map_add, Polynomial.map_add,
      Polynomial.map_mul, Polynomial.map_mul, Polynomial.map_pow,
      Polynomial.map_C, Polynomial.map_C, Polynomial.map_C,
      Polynomial.map_X] at hy
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X, Polynomial.eval_pow] at hy
    change (B.coeff 0).eval z + (B.coeff 1).eval z * y +
      (B.coeff 2).eval z * y ^ 2 = 0 at hy
    exact hy
  have hsquare : (B.coeff 2).eval z * (y - L.eval z) ^ 2 = 0 := by
    linear_combination hy' - hrootz - (y - L.eval z) * hderivz
  have : (y - L.eval z) ^ 2 = 0 := (mul_eq_zero.mp hsquare).resolve_left hquad
  exact sub_eq_zero.mp (sq_eq_zero_iff.mp this)

/-- When a quadratic relation drops to a genuine linear relation at `z`, its
specialized root is again the affine graph root. -/
theorem degree_drop_linear_specialized_root_unique
    (B : F[X][X]) (L : F[X]) (z y : F)
    (hdeg : B.natDegree ≤ 2)
    (hroot : B.eval L = 0)
    (hquadZero : (B.coeff 2).eval z = 0)
    (hlinear : (B.coeff 1).eval z ≠ 0)
    (hy : (B.map (Polynomial.evalRingHom z)).eval y = 0) :
    y = L.eval z := by
  have hshape : B =
      Polynomial.C (B.coeff 0) +
        Polynomial.C (B.coeff 1) * Polynomial.X +
          Polynomial.C (B.coeff 2) * Polynomial.X ^ 2 := by
    ext n
    rcases n with _ | n
    · simp
    rcases n with _ | n
    · simp
    rcases n with _ | n
    · simp
    · have hn : B.natDegree < n.succ.succ.succ := by omega
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt hn]
      simp
  have hrootz :
      (B.coeff 0).eval z + (B.coeff 1).eval z * L.eval z +
          (B.coeff 2).eval z * (L.eval z) ^ 2 = 0 := by
    rw [hshape] at hroot
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X, Polynomial.eval_pow] at hroot
    have hz := congrArg (Polynomial.eval z) hroot
    simpa only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_zero] using hz
  have hy' :
      (B.coeff 0).eval z + (B.coeff 1).eval z * y +
          (B.coeff 2).eval z * y ^ 2 = 0 := by
    rw [hshape, Polynomial.map_add, Polynomial.map_add,
      Polynomial.map_mul, Polynomial.map_mul, Polynomial.map_pow,
      Polynomial.map_C, Polynomial.map_C, Polynomial.map_C,
      Polynomial.map_X] at hy
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X, Polynomial.eval_pow] at hy
    change (B.coeff 0).eval z + (B.coeff 1).eval z * y +
      (B.coeff 2).eval z * y ^ 2 = 0 at hy
    exact hy
  have hdiff : (B.coeff 1).eval z * (y - L.eval z) = 0 := by
    rw [hquadZero] at hrootz hy'
    linear_combination hy' - hrootz
  exact sub_eq_zero.mp ((mul_eq_zero.mp hdiff).resolve_left hlinear)

/-- Unified local adapter for the two clean-coordinate cases used by the
sparse-dirty proof. -/
theorem quadratic_or_degree_drop_specialized_root_unique
    (B : F[X][X]) (L : F[X]) (z y : F)
    (hdeg : B.natDegree ≤ 2)
    (hroot : B.eval L = 0)
    (hclean : ((B.coeff 2).eval z ≠ 0 ∧
        B.derivative.eval L = 0) ∨
      ((B.coeff 2).eval z = 0 ∧ (B.coeff 1).eval z ≠ 0))
    (hy : (B.map (Polynomial.evalRingHom z)).eval y = 0) :
    y = L.eval z := by
  rcases hclean with ⟨hquad, hderiv⟩ | ⟨hquad, hlinear⟩
  · exact quadratic_specialized_root_unique
      B L z y hdeg hroot hderiv hquad hy
  · exact degree_drop_linear_specialized_root_unique
      B L z y hdeg hroot hquad hlinear hy

/-- Root-counting bound for sparse dirty-coordinate sets.  Each coordinate
polynomial contributes at most `B` dirty challenges. -/
theorem sparse_bad_seed_count
    {I : Type} [Fintype I] [DecidableEq I] [DecidableEq F]
    (W : Finset I) (T : Finset F) (G : I → F[X])
    (B b : ℕ)
    (hne : ∀ i ∈ W, G i ≠ 0)
    (hdeg : ∀ i ∈ W, (G i).natDegree ≤ B) :
    let Bad : F → Finset I := fun z =>
      W.filter fun i => (G i).eval z = 0
    (b + 1) * (T.filter fun z => b < (Bad z).card).card ≤
      W.card * B := by
  classical
  let Bad : F → Finset I := fun z =>
    W.filter fun i => (G i).eval z = 0
  let Large : Finset F := T.filter fun z => b < (Bad z).card
  have hfiber : ∀ i ∈ W,
      (T.filter fun z => i ∈ Bad z).card ≤ B := by
    intro i hi
    have hsub : (T.filter fun z => i ∈ Bad z) ⊆ (G i).roots.toFinset := by
      intro z hz
      have hz' := Finset.mem_filter.mp hz
      have hzi := (Finset.mem_filter.mp hz'.2).2
      rw [Multiset.mem_toFinset, Polynomial.mem_roots (hne i hi)]
      exact hzi
    calc
      (T.filter fun z => i ∈ Bad z).card
          ≤ (G i).roots.toFinset.card := Finset.card_le_card hsub
      _ ≤ (G i).roots.card := Multiset.toFinset_card_le _
      _ ≤ (G i).natDegree := Polynomial.card_roots' _
      _ ≤ B := hdeg i hi
  have hlower : (b + 1) * Large.card ≤
      ∑ z ∈ T, (Bad z).card := by
    calc
      (b + 1) * Large.card = ∑ z ∈ Large, (b + 1) := by
        simp [mul_comm]
      _ ≤ ∑ z ∈ Large, (Bad z).card := by
        apply Finset.sum_le_sum
        intro z hz
        exact (Finset.mem_filter.mp hz).2
      _ ≤ ∑ z ∈ T, (Bad z).card :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (by simp)
  have hupper : (∑ z ∈ T, (Bad z).card) ≤ W.card * B := by
    rw [sum_card_eq_sum_fiber_card T Bad]
    calc
      (∑ i : I, (T.filter fun z => i ∈ Bad z).card) =
          ∑ i ∈ W, (T.filter fun z => i ∈ Bad z).card := by
        symm
        apply Finset.sum_subset (Finset.subset_univ W)
        intro i _ hi
        simp [Bad, hi]
      _ ≤ ∑ _i ∈ W, B := Finset.sum_le_sum hfiber
      _ = W.card * B := by simp
  exact hlower.trans hupper

/-- If every challenge is dirty at at most `b` coordinates, then any two
distinct challenges determine one polynomial pencil containing all sections,
provided three dirty sets still leave more interpolation points than the row
degree. -/
theorem sparseBad_pencil_alignment
    [DecidableEq F] (T W : Finset F) (D b : ℕ)
    (sect : F → F[X]) (line₀ line₁ : F → F)
    (Bad : F → Finset F)
    (hdeg : ∀ z ∈ T, (sect z).natDegree ≤ D)
    (hBad : ∀ z ∈ T, (Bad z).card ≤ b)
    (hW : D + 3 * b < W.card)
    (hagree : ∀ z ∈ T, ∀ x ∈ W \ Bad z,
      (sect z).eval x = line₀ x + z * line₁ x)
    {z₀ z₁ : F} (hz₀ : z₀ ∈ T) (hz₁ : z₁ ∈ T)
    (hne : z₀ ≠ z₁) :
    ∃ p₀ p₁ : F[X], p₀.natDegree ≤ D ∧ p₁.natDegree ≤ D ∧
      ∀ z ∈ T, sect z = p₀ + Polynomial.C z * p₁ := by
  classical
  let p₁ : F[X] := Polynomial.C (z₁ - z₀)⁻¹ * (sect z₁ - sect z₀)
  let p₀ : F[X] := sect z₀ - Polynomial.C z₀ * p₁
  have hdiff : z₁ - z₀ ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
  have hp₁ : p₁.natDegree ≤ D := by
    exact (Polynomial.natDegree_C_mul_le _ _).trans
      ((Polynomial.natDegree_sub_le _ _).trans (max_le (hdeg z₁ hz₁) (hdeg z₀ hz₀)))
  have hp₀ : p₀.natDegree ≤ D := by
    exact (Polynomial.natDegree_sub_le _ _).trans
      (max_le (hdeg z₀ hz₀) ((Polynomial.natDegree_C_mul_le _ _).trans hp₁))
  refine ⟨p₀, p₁, hp₀, hp₁, ?_⟩
  intro z hz
  let Common : Finset F := W \ (Bad z ∪ Bad z₀ ∪ Bad z₁)
  have hunion : (Bad z ∪ Bad z₀ ∪ Bad z₁).card ≤ 3 * b := by
    calc
      (Bad z ∪ Bad z₀ ∪ Bad z₁).card
          ≤ (Bad z ∪ Bad z₀).card + (Bad z₁).card :=
            Finset.card_union_le _ _
      _ ≤ ((Bad z).card + (Bad z₀).card) + (Bad z₁).card := by
            gcongr
            exact Finset.card_union_le _ _
      _ ≤ 3 * b := by
            have hzbad := hBad z hz
            have hz₀bad := hBad z₀ hz₀
            have hz₁bad := hBad z₁ hz₁
            omega
  have hCommon : D < Common.card := by
    have hinter : (W ∩ (Bad z ∪ Bad z₀ ∪ Bad z₁)).card ≤ 3 * b :=
      (Finset.card_le_card Finset.inter_subset_right).trans hunion
    have hsplit := Finset.card_sdiff_add_card_inter W
      (Bad z ∪ Bad z₀ ∪ Bad z₁)
    dsimp [Common]
    omega
  have hpencil : (p₀ + Polynomial.C z * p₁).natDegree ≤ D :=
    (Polynomial.natDegree_add_le _ _).trans
      (max_le hp₀ ((Polynomial.natDegree_C_mul_le _ _).trans hp₁))
  apply Polynomial.eq_of_natDegree_lt_card_of_eval_eq'
      (sect z) (p₀ + Polynomial.C z * p₁) Common
  · intro x hx
    have hx' := Finset.mem_sdiff.mp hx
    have hxz : x ∈ W \ Bad z := Finset.mem_sdiff.mpr ⟨hx'.1, by
      intro h
      exact hx'.2 (Finset.mem_union_left _ (Finset.mem_union_left _ h))⟩
    have hxz₀ : x ∈ W \ Bad z₀ := Finset.mem_sdiff.mpr ⟨hx'.1, by
      intro h
      exact hx'.2 (Finset.mem_union_left _ (Finset.mem_union_right _ h))⟩
    have hxz₁ : x ∈ W \ Bad z₁ := Finset.mem_sdiff.mpr ⟨hx'.1, by
      intro h
      exact hx'.2 (Finset.mem_union_right _ h)⟩
    have ha := hagree z hz x hxz
    have ha₀ := hagree z₀ hz₀ x hxz₀
    have ha₁ := hagree z₁ hz₁ x hxz₁
    dsimp [p₀, p₁]
    simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
      Polynomial.eval_C]
    rw [ha, ha₀, ha₁]
    field_simp [hdiff]
    ring
  · exact (max_le (hdeg z hz) hpencil).trans_lt hCommon

/-- Score-64 specialization of the three-way dirty-set alignment theorem. -/
theorem sparseBad_pencil_alignment_6400
    [DecidableEq F] (T W : Finset F)
    (sect : F → F[X]) (line₀ line₁ : F → F)
    (Bad : F → Finset F)
    (hWcard : W.card = 131413)
    (hdeg : ∀ z ∈ T, (sect z).natDegree ≤ 131071)
    (hBad : ∀ z ∈ T, (Bad z).card ≤ 113)
    (hagree : ∀ z ∈ T, ∀ x ∈ W \ Bad z,
      (sect z).eval x = line₀ x + z * line₁ x)
    {z₀ z₁ : F} (hz₀ : z₀ ∈ T) (hz₁ : z₁ ∈ T)
    (hne : z₀ ≠ z₁) :
    ∃ p₀ p₁ : F[X], p₀.natDegree ≤ 131071 ∧
      p₁.natDegree ≤ 131071 ∧
      ∀ z ∈ T, sect z = p₀ + Polynomial.C z * p₁ := by
  apply sparseBad_pencil_alignment T W 131071 113
    sect line₀ line₁ Bad hdeg hBad
  · omega
  · exact hagree
  · exact hz₀
  · exact hz₁
  · exact hne

/-- Exact arithmetic used by the score-64 sparse-dirty branch. -/
theorem sparse_bad_score6400_exact_margin
    (tcard bad good : ℕ)
    (hT : 1133 * 2 * 1898945373 < tcard)
    (hpart : good + bad = tcard)
    (hbad : 114 * bad ≤ 131413 * 1898945373) :
    2114009265202 ≤ good := by
  norm_num at hT hbad ⊢
  omega

/-- The exact margin is far above the `76,781` selected rows required by the
score-64 branch. -/
theorem sparse_bad_score6400_numeric
    (tcard bad good : ℕ)
    (hT : 1133 * 2 * 1898945373 < tcard)
    (hpart : good + bad = tcard)
    (hbad : 114 * bad ≤ 131413 * 1898945373) :
    76781 < good := by
  have hmargin := sparse_bad_score6400_exact_margin
    tcard bad good hT hpart hbad
  omega

/-- Root counting constructs the large clean row set consumed by the
score-64 pencil theorem. -/
theorem exists_sparse_good_seeds_6400
    {I : Type} [Fintype I] [DecidableEq I] [DecidableEq F]
    (W : Finset I) (T : Finset F) (G : I → F[X])
    (hWcard : W.card = 131413)
    (hne : ∀ i ∈ W, G i ≠ 0)
    (hdeg : ∀ i ∈ W, (G i).natDegree ≤ 1898945373)
    (hT : 1133 * 2 * 1898945373 < T.card) :
    ∃ Good : Finset F,
      Good ⊆ T ∧ 2114009265202 ≤ Good.card ∧
        ∀ z ∈ Good,
          (W.filter fun i => (G i).eval z = 0).card ≤ 113 := by
  classical
  let Bad : F → Finset I := fun z =>
    W.filter fun i => (G i).eval z = 0
  let Good : Finset F := T.filter fun z => (Bad z).card ≤ 113
  have hbad := sparse_bad_seed_count W T G 1898945373 113 hne hdeg
  change 114 * (T.filter fun z => 113 < (Bad z).card).card ≤
    W.card * 1898945373 at hbad
  rw [hWcard] at hbad
  have hpart : Good.card +
      (T.filter fun z => 113 < (Bad z).card).card = T.card := by
    simpa only [Good, not_le] using
      (Finset.card_filter_add_card_filter_not
        (s := T) (p := fun z => (Bad z).card ≤ 113))
  have hmargin : 2114009265202 ≤ Good.card :=
    sparse_bad_score6400_exact_margin T.card
      (T.filter fun z => 113 < (Bad z).card).card Good.card
        hT hpart hbad
  refine ⟨Good, Finset.filter_subset _ _, hmargin, ?_⟩
  intro z hz
  exact (Finset.mem_filter.mp hz).2

/-- Complete combinatorial assembly of the sparse-dirty branch.  Once each
coordinate supplies its nonzero challenge polynomial `G`, every clean row is
forced onto one common polynomial pencil. -/
theorem sparse_dirty_pencil_6400
    [Fintype F] [DecidableEq F]
    (W T : Finset F) (G : F → F[X])
    (sect : F → F[X]) (line₀ line₁ : F → F)
    (hWcard : W.card = 131413)
    (hGne : ∀ x ∈ W, G x ≠ 0)
    (hGdeg : ∀ x ∈ W, (G x).natDegree ≤ 1898945373)
    (hT : 1133 * 2 * 1898945373 < T.card)
    (hsectdeg : ∀ z ∈ T, (sect z).natDegree ≤ 131071)
    (hcleanAgreement : ∀ z ∈ T, ∀ x ∈ W,
      (G x).eval z ≠ 0 →
        (sect z).eval x = line₀ x + z * line₁ x) :
    ∃ Good : Finset F, ∃ p₀ p₁ : F[X],
      Good ⊆ T ∧ 2114009265202 ≤ Good.card ∧
      p₀.natDegree ≤ 131071 ∧ p₁.natDegree ≤ 131071 ∧
      ∀ z ∈ Good, sect z = p₀ + Polynomial.C z * p₁ := by
  classical
  obtain ⟨Good, hGoodT, hGoodCard, hGoodBad⟩ :=
    exists_sparse_good_seeds_6400 W T G hWcard hGne hGdeg hT
  have htwo : 1 < Good.card := by omega
  obtain ⟨z₀, hz₀, z₁, hz₁, hne⟩ := Finset.one_lt_card.mp htwo
  let Bad : F → Finset F := fun z =>
    W.filter fun x => (G x).eval z = 0
  obtain ⟨p₀, p₁, hp₀, hp₁, hpencil⟩ :=
    sparseBad_pencil_alignment_6400 Good W sect line₀ line₁ Bad
      hWcard
      (fun z hz => hsectdeg z (hGoodT hz))
      (fun z hz => by simpa only [Bad] using hGoodBad z hz)
      (by
        intro z hz x hx
        have hx' := Finset.mem_sdiff.mp hx
        apply hcleanAgreement z (hGoodT hz) x hx'.1
        intro hzero
        exact hx'.2 (Finset.mem_filter.mpr ⟨hx'.1, hzero⟩))
      hz₀ hz₁ hne
  exact ⟨Good, p₀, p₁, hGoodT, hGoodCard,
    hp₀, hp₁, hpencil⟩

/-- Algebraic-to-combinatorial assembly for the high-identity quadratic
branch.  The remaining producer obligation is precisely the construction of
the coordinate relations `B`, affine roots `L`, and nonzero cleanup
polynomials `G` satisfying these local hypotheses. -/
theorem sparse_dirty_quadratic_pencil_6400
    [Fintype F] [DecidableEq F]
    (W T : Finset F) (G : F → F[X])
    (B : F → F[X][X]) (L : F → F[X])
    (sect : F → F[X]) (line₀ line₁ : F → F)
    (hWcard : W.card = 131413)
    (hGne : ∀ x ∈ W, G x ≠ 0)
    (hGdeg : ∀ x ∈ W, (G x).natDegree ≤ 1898945373)
    (hT : 1133 * 2 * 1898945373 < T.card)
    (hsectdeg : ∀ z ∈ T, (sect z).natDegree ≤ 131071)
    (hL : ∀ x ∈ W, L x =
      Polynomial.C (line₀ x) + Polynomial.X * Polynomial.C (line₁ x))
    (hBdeg : ∀ x ∈ W, (B x).natDegree ≤ 2)
    (hBroot : ∀ x ∈ W, (B x).eval (L x) = 0)
    (hclean : ∀ z ∈ T, ∀ x ∈ W, (G x).eval z ≠ 0 →
      (((B x).coeff 2).eval z ≠ 0 ∧
          (B x).derivative.eval (L x) = 0) ∨
        (((B x).coeff 2).eval z = 0 ∧
          ((B x).coeff 1).eval z ≠ 0))
    (hsectionRoot : ∀ z ∈ T, ∀ x ∈ W,
      ((B x).map (Polynomial.evalRingHom z)).eval
        ((sect z).eval x) = 0) :
    ∃ Good : Finset F, ∃ p₀ p₁ : F[X],
      Good ⊆ T ∧ 2114009265202 ≤ Good.card ∧
      p₀.natDegree ≤ 131071 ∧ p₁.natDegree ≤ 131071 ∧
      ∀ z ∈ Good, sect z = p₀ + Polynomial.C z * p₁ := by
  apply sparse_dirty_pencil_6400 W T G sect line₀ line₁
    hWcard hGne hGdeg hT hsectdeg
  intro z hz x hx hGclean
  have hrootEq := quadratic_or_degree_drop_specialized_root_unique
    (B x) (L x) z ((sect z).eval x)
      (hBdeg x hx) (hBroot x hx) (hclean z hz x hx hGclean)
      (hsectionRoot z hz x hx)
  calc
    (sect z).eval x = (L x).eval z := hrootEq
    _ = line₀ x + z * line₁ x := by
      rw [hL x hx]
      simp only [Polynomial.eval_add, Polynomial.eval_C,
        Polynomial.eval_mul, Polynomial.eval_X]

/-- A coefficient cleanup polynomial for a generically repeated quadratic
section.  The linear coefficient is preferred; if it vanishes identically,
the quadratic coefficient is necessarily nonzero. -/
noncomputable def quadraticRepeatedCleanup (B : F[X][X]) : F[X] :=
  by
    classical
    exact if B.coeff 1 ≠ 0 then B.coeff 1 else B.coeff 2

/-- The cleanup polynomial of a nonzero repeated quadratic section is
nonzero.  This is the small algebraic producer needed by the sparse-dirty
branch; it avoids charging a resultant. -/
theorem quadraticRepeatedCleanup_ne_zero
    (B : F[X][X]) (L : F[X])
    (hB : B ≠ 0) (hdeg : B.natDegree ≤ 2)
    (hroot : B.eval L = 0) :
    quadraticRepeatedCleanup B ≠ 0 := by
  classical
  by_cases h1 : B.coeff 1 ≠ 0
  · simpa [quadraticRepeatedCleanup, h1]
  · simp only [quadraticRepeatedCleanup, if_neg h1]
    intro h2
    apply hB
    have hshape : B =
        Polynomial.C (B.coeff 0) +
          Polynomial.C (B.coeff 1) * Polynomial.X +
            Polynomial.C (B.coeff 2) * Polynomial.X ^ 2 := by
      ext n
      rcases n with _ | n
      · simp
      rcases n with _ | n
      · simp
      rcases n with _ | n
      · simp
      · have hn : B.natDegree < n.succ.succ.succ := by omega
        rw [Polynomial.coeff_eq_zero_of_natDegree_lt hn]
        simp
    have h1zero : B.coeff 1 = 0 := not_ne_iff.mp h1
    have h0 : B.coeff 0 = 0 := by
      rw [hshape] at hroot
      simp only [Polynomial.eval_add, Polynomial.eval_mul,
        Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_pow] at hroot
      rw [h1zero, h2] at hroot
      simp at hroot
      exact hroot
    rw [hshape, h0, h1zero, h2]
    simp

/-- At every challenge not killed by the cleanup polynomial, a repeated
quadratic section has the exact local uniqueness shape consumed by
`quadratic_or_degree_drop_specialized_root_unique`. -/
theorem quadraticRepeatedCleanup_clean
    [DecidableEq F] (B : F[X][X]) (L : F[X]) (z : F)
    (hderiv : B.derivative.eval L = 0)
    (hclean : (quadraticRepeatedCleanup B).eval z ≠ 0) :
    ((B.coeff 2).eval z ≠ 0 ∧ B.derivative.eval L = 0) ∨
      ((B.coeff 2).eval z = 0 ∧ (B.coeff 1).eval z ≠ 0) := by
  classical
  by_cases h1 : B.coeff 1 ≠ 0
  · have h1z : (B.coeff 1).eval z ≠ 0 := by
      simpa [quadraticRepeatedCleanup, h1] using hclean
    by_cases h2z : (B.coeff 2).eval z ≠ 0
    · exact Or.inl ⟨h2z, hderiv⟩
    · exact Or.inr ⟨not_ne_iff.mp h2z, h1z⟩
  · have h2z : (B.coeff 2).eval z ≠ 0 := by
      simpa [quadraticRepeatedCleanup, h1] using hclean
    exact Or.inl ⟨h2z, hderiv⟩

/-- Complete producer for the nonsimple quadratic score-64 branch.

Once the fixed trivariate factor gives a nonzero quadratic coordinate parent
whose affine graph is a repeated generic root on `W`, the linear/quadratic
coefficient cleanup has degree at most `D`.  Root counting and the existing
sparse-dirty assembly then put all retained sections on one polynomial
pencil. -/
theorem repeated_quadratic_sparse_dirty_pencil_6400
    [Fintype F] [DecidableEq F]
    (W T : Finset F) (B : F → F[X][X]) (L : F → F[X])
    (sect : F → F[X]) (line₀ line₁ : F → F) (D : ℕ)
    (hWcard : W.card = 131413)
    (hD : D ≤ 1898945373)
    (hT : 1133 * 2 * 1898945373 < T.card)
    (hsectdeg : ∀ z ∈ T, (sect z).natDegree ≤ 131071)
    (hL : ∀ x ∈ W, L x =
      Polynomial.C (line₀ x) + Polynomial.X * Polynomial.C (line₁ x))
    (hBne : ∀ x ∈ W, B x ≠ 0)
    (hBdeg : ∀ x ∈ W, (B x).natDegree ≤ 2)
    (hBXdeg : ∀ x ∈ W, Polynomial.Bivariate.degreeX (B x) ≤ D)
    (hBroot : ∀ x ∈ W, (B x).eval (L x) = 0)
    (hBrepeated : ∀ x ∈ W, (B x).derivative.eval (L x) = 0)
    (hsectionRoot : ∀ z ∈ T, ∀ x ∈ W,
      ((B x).map (Polynomial.evalRingHom z)).eval
        ((sect z).eval x) = 0) :
    ∃ Good : Finset F, ∃ p₀ p₁ : F[X],
      Good ⊆ T ∧ 2114009265202 ≤ Good.card ∧
      p₀.natDegree ≤ 131071 ∧ p₁.natDegree ≤ 131071 ∧
      ∀ z ∈ Good, sect z = p₀ + Polynomial.C z * p₁ := by
  let G : F → F[X] := fun x ↦ quadraticRepeatedCleanup (B x)
  apply sparse_dirty_quadratic_pencil_6400 W T G B L sect line₀ line₁
    hWcard
  · intro x hx
    exact quadraticRepeatedCleanup_ne_zero (B x) (L x)
      (hBne x hx) (hBdeg x hx) (hBroot x hx)
  · intro x hx
    dsimp only [G]
    by_cases h1 : (B x).coeff 1 ≠ 0
    · simpa [quadraticRepeatedCleanup, h1] using
        ((Polynomial.Bivariate.coeff_natDegree_le_degreeX (B x) 1).trans
          (hBXdeg x hx)).trans hD
    · simpa [quadraticRepeatedCleanup, h1] using
        ((Polynomial.Bivariate.coeff_natDegree_le_degreeX (B x) 2).trans
          (hBXdeg x hx)).trans hD
  · exact hT
  · exact hsectdeg
  · exact hL
  · exact hBdeg
  · exact hBroot
  · intro z hz x hx hclean
    exact quadraticRepeatedCleanup_clean (B x) (L x) z
      (hBrepeated x hx) hclean
  · exact hsectionRoot

/-! ## Linear coordinate parents

The degree-one selected-factor branch is simpler than the repeated quadratic
branch above.  Its linear coefficient is itself a nonzero cleanup polynomial,
and outside its roots the affine graph is the unique specialized root. -/

/-- A nonzero polynomial of outer degree at most one which has a polynomial
root must have a nonzero linear coefficient. -/
theorem linearCoeff_ne_zero_of_root
    (B : F[X][X]) (L : F[X])
    (hB : B ≠ 0) (hdeg : B.natDegree ≤ 1)
    (hroot : B.eval L = 0) :
    B.coeff 1 ≠ 0 := by
  intro h1
  have hshape : B =
      Polynomial.C (B.coeff 0) + Polynomial.C (B.coeff 1) * Polynomial.X := by
    ext n
    rcases n with _ | n
    · simp
    rcases n with _ | n
    · simp
    · have hn : B.natDegree < n.succ.succ := by omega
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt hn]
      simp
  have h0 : B.coeff 0 = 0 := by
    rw [hshape] at hroot
    simp only [Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_X] at hroot
    rw [h1] at hroot
    simpa using hroot
  apply hB
  rw [hshape, h0, h1]
  simp

/-- Complete sparse-dirty producer for coordinate parents of degree at most
one.  Compared with a resultant argument, only one coefficient polynomial of
degree `D` is charged per coordinate. -/
theorem linear_sparse_dirty_pencil_6400
    [Fintype F] [DecidableEq F]
    (W T : Finset F) (B : F → F[X][X]) (L : F → F[X])
    (sect : F → F[X]) (line₀ line₁ : F → F) (D : ℕ)
    (hWcard : W.card = 131413)
    (hD : D ≤ 1898945373)
    (hT : 1133 * 2 * 1898945373 < T.card)
    (hsectdeg : ∀ z ∈ T, (sect z).natDegree ≤ 131071)
    (hL : ∀ x ∈ W, L x =
      Polynomial.C (line₀ x) + Polynomial.X * Polynomial.C (line₁ x))
    (hBne : ∀ x ∈ W, B x ≠ 0)
    (hBdeg : ∀ x ∈ W, (B x).natDegree ≤ 1)
    (hBXdeg : ∀ x ∈ W, Polynomial.Bivariate.degreeX (B x) ≤ D)
    (hBroot : ∀ x ∈ W, (B x).eval (L x) = 0)
    (hsectionRoot : ∀ z ∈ T, ∀ x ∈ W,
      ((B x).map (Polynomial.evalRingHom z)).eval
        ((sect z).eval x) = 0) :
    ∃ Good : Finset F, ∃ p₀ p₁ : F[X],
      Good ⊆ T ∧ 2114009265202 ≤ Good.card ∧
      p₀.natDegree ≤ 131071 ∧ p₁.natDegree ≤ 131071 ∧
      ∀ z ∈ Good, sect z = p₀ + Polynomial.C z * p₁ := by
  let G : F → F[X] := fun x ↦ (B x).coeff 1
  apply sparse_dirty_pencil_6400 W T G sect line₀ line₁
    hWcard
  · intro x hx
    exact linearCoeff_ne_zero_of_root (B x) (L x)
      (hBne x hx) (hBdeg x hx) (hBroot x hx)
  · intro x hx
    exact ((Polynomial.Bivariate.coeff_natDegree_le_degreeX (B x) 1).trans
      (hBXdeg x hx)).trans hD
  · exact hT
  · exact hsectdeg
  · intro z hz x hx hclean
    have hquad : ((B x).coeff 2).eval z = 0 := by
      have hcoeff : (B x).coeff 2 = 0 := by
        exact Polynomial.coeff_eq_zero_of_natDegree_lt (by
          have := hBdeg x hx
          omega)
      simp [hcoeff]
    have hlinear : ((B x).coeff 1).eval z ≠ 0 := hclean
    have hrootEq := degree_drop_linear_specialized_root_unique
      (B x) (L x) z ((sect z).eval x) (by
        exact (hBdeg x hx).trans (by omega))
      (hBroot x hx) hquad hlinear (hsectionRoot z hz x hx)
    calc
      (sect z).eval x = (L x).eval z := hrootEq
      _ = line₀ x + z * line₁ x := by
        rw [hL x hx]
        simp only [Polynomial.eval_add, Polynomial.eval_C,
          Polynomial.eval_mul, Polynomial.eval_X]

end ProximityPrize.SubmissionLower
