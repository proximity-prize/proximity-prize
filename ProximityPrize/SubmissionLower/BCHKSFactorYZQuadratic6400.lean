import ProximityPrize.SubmissionLower.BCHKSSimpleSetOwner6400

/-!
# Factor-specific quadratic closure at score 64.00

This module combines the branch-free simple-locus owner theorem with the
finite repeated-quadratic cleanup.  All root-counting charges use the selected
factor's own additive `Y+Z` cap `D`.
-/

namespace ProximityPrize.SubmissionLower

open Polynomial
open RationalFunctions.HenselNumerators.ConcreteFiniteNumerators

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

variable {F : Type} [Field F]

/-- With the factor-specific seed coefficient, deleting every row having
more than 113 dirty coordinates still leaves more than 76,780 rows. -/
theorem factorYZ_sparse_bad_numeric_6400
    (t bad good D : ℕ) (hD : 0 < D)
    (hT : 144802557 * D < t)
    (hpart : good + bad = t)
    (hbad : 114 * bad ≤ 131413 * D) :
    76780 < good := by
  norm_num at hT hbad ⊢
  nlinarith

/-- Sparse-dirty pencil assembly with an arbitrary factor-specific degree
cap. -/
theorem factorYZ_sparse_dirty_pencil_6400
    [Fintype F] [DecidableEq F]
    (W T : Finset F) (G : F → F[X])
    (sect : F → F[X]) (line₀ line₁ : F → F) (D : ℕ)
    (hWcard : W.card = 131413)
    (hD : 0 < D)
    (hGne : ∀ x ∈ W, G x ≠ 0)
    (hGdeg : ∀ x ∈ W, (G x).natDegree ≤ D)
    (hT : 144802557 * D < T.card)
    (hsectdeg : ∀ z ∈ T, (sect z).natDegree ≤ 131071)
    (hcleanAgreement : ∀ z ∈ T, ∀ x ∈ W,
      (G x).eval z ≠ 0 →
        (sect z).eval x = line₀ x + z * line₁ x) :
    ∃ Good : Finset F, ∃ p₀ p₁ : F[X],
      Good ⊆ T ∧ 76780 < Good.card ∧
      p₀.natDegree ≤ 131071 ∧ p₁.natDegree ≤ 131071 ∧
      ∀ z ∈ Good, sect z = p₀ + Polynomial.C z * p₁ := by
  classical
  let Bad : F → Finset F := fun z =>
    W.filter fun x => (G x).eval z = 0
  let Good : Finset F := T.filter fun z => (Bad z).card ≤ 113
  have hbadCount := sparse_bad_seed_count W T G D 113 hGne hGdeg
  change 114 * (T.filter fun z => 113 < (Bad z).card).card ≤
    W.card * D at hbadCount
  rw [hWcard] at hbadCount
  have hpart : Good.card +
      (T.filter fun z => 113 < (Bad z).card).card = T.card := by
    simpa only [Good, not_le] using
      (Finset.card_filter_add_card_filter_not
        (s := T) (p := fun z => (Bad z).card ≤ 113))
  have hGoodCard : 76780 < Good.card :=
    factorYZ_sparse_bad_numeric_6400 T.card
      (T.filter fun z => 113 < (Bad z).card).card Good.card D
      hD hT hpart hbadCount
  have hGoodBad : ∀ z ∈ Good, (Bad z).card ≤ 113 := by
    intro z hz
    exact (Finset.mem_filter.mp hz).2
  have hGoodT : Good ⊆ T := by
    intro z hz
    exact (Finset.mem_filter.mp hz).1
  have htwo : 1 < Good.card := by omega
  obtain ⟨z₀, hz₀, z₁, hz₁, hne⟩ := Finset.one_lt_card.mp htwo
  obtain ⟨p₀, p₁, hp₀, hp₁, hpencil⟩ :=
    sparseBad_pencil_alignment_6400 Good W sect line₀ line₁ Bad
      hWcard
      (fun z hz => hsectdeg z (hGoodT hz))
      hGoodBad
      (by
        intro z hz x hx
        have hx' := Finset.mem_sdiff.mp hx
        apply hcleanAgreement z (hGoodT hz) x hx'.1
        intro hzero
        exact hx'.2 (Finset.mem_filter.mpr ⟨hx'.1, hzero⟩))
      hz₀ hz₁ hne
  exact ⟨Good, p₀, p₁, hGoodT, hGoodCard,
    hp₀, hp₁, hpencil⟩

/-- Repeated-quadratic producer using the selected factor's own `Y+Z` cap. -/
theorem factorYZ_repeated_quadratic_pencil_6400
    [Fintype F] [DecidableEq F]
    (W T : Finset F) (B : F → F[X][X]) (L : F → F[X])
    (sect : F → F[X]) (line₀ line₁ : F → F) (D : ℕ)
    (hWcard : W.card = 131413)
    (hD : 0 < D)
    (hT : 144802557 * D < T.card)
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
      Good ⊆ T ∧ 76780 < Good.card ∧
      p₀.natDegree ≤ 131071 ∧ p₁.natDegree ≤ 131071 ∧
      ∀ z ∈ Good, sect z = p₀ + Polynomial.C z * p₁ := by
  let G : F → F[X] := fun x ↦ quadraticRepeatedCleanup (B x)
  apply factorYZ_sparse_dirty_pencil_6400
    W T G sect line₀ line₁ D hWcard hD
  · intro x hx
    exact quadraticRepeatedCleanup_ne_zero (B x) (L x)
      (hBne x hx) (hBdeg x hx) (hBroot x hx)
  · intro x hx
    dsimp only [G]
    by_cases h1 : (B x).coeff 1 ≠ 0
    · simpa [quadraticRepeatedCleanup, h1] using
        (Polynomial.Bivariate.coeff_natDegree_le_degreeX (B x) 1).trans
          (hBXdeg x hx)
    · simpa [quadraticRepeatedCleanup, h1] using
        (Polynomial.Bivariate.coeff_natDegree_le_degreeX (B x) 2).trans
          (hBXdeg x hx)
  · exact hT
  · exact hsectdeg
  · intro z hz x hx hclean
    have hshape := quadraticRepeatedCleanup_clean (B x) (L x) z
      (hBrepeated x hx) hclean
    have hrootEq := quadratic_or_degree_drop_specialized_root_unique
      (B x) (L x) z ((sect z).eval x)
      (hBdeg x hx) (hBroot x hx) hshape (hsectionRoot z hz x hx)
    calc
      (sect z).eval x = (L x).eval z := hrootEq
      _ = line₀ x + z * line₁ x := by
        rw [hL x hx]
        simp only [Polynomial.eval_add, Polynomial.eval_C,
          Polynomial.eval_mul, Polynomial.eval_X]

/-- A high-identity irreducible quadratic factor closes at score 64 without
selecting a global Hensel branch: many simple identities use the universal
owner core, while many repeated identities use finite quadratic uniqueness. -/
theorem fixed_factor_quadratic_high_identity_alignment_factorYZ6400
    {I F : Type} [Fintype I] [DecidableEq I]
    [Field F] [Fintype F] [DecidableEq F]
    (omega : I ↪ F) (hn : Fintype.card I = 262144)
    (R : F[X][X][X]) (hRirr : Irreducible R)
    (hRdegree : R.natDegree = 2)
    (D : ℕ) (hD : 2 ≤ D) (hYZ : YZCap R D)
    (T : Finset F) (P : F → F[X]) (A : F → Finset I)
    (U₀ U₁ : I → F)
    (hPdegree : ∀ z ∈ T, (P z).natDegree ≤ 131071)
    (hvan : ∀ z ∈ T, triEval R z (P z) = 0)
    (hrow : ∀ z ∈ T, 185364 ≤ (A z).card)
    (hagreement : ∀ z ∈ T, ∀ i ∈ A z,
      (P z).eval (omega i) = U₀ i + z * U₁ i)
    (hT : 144802557 * D < T.card)
    (hhigh : 212478 < (Finset.univ.filter fun i : I ↦
      directAffineObstruction R (omega i) (U₀ i) (U₁ i) = 0).card)
    (hkF : 131071 < Fintype.card F) :
    ∃ Good : Finset F, ∃ p₀ p₁ : F[X],
      Good ⊆ T ∧ 76780 < Good.card ∧
      p₀.natDegree ≤ 131071 ∧ p₁.natDegree ≤ 131071 ∧
      ∀ z ∈ Good, P z = p₀ + Polynomial.C z * p₁ := by
  classical
  let G : I → F[X] := fun i =>
    directAffineObstruction R (omega i) (U₀ i) (U₁ i)
  let Identity : Finset I := Finset.univ.filter fun i => G i = 0
  let BI : I → F[X][X] := fun i => triSpecializeX R (omega i)
  let LI : I → F[X] := fun i =>
    Polynomial.C (U₀ i) + Polynomial.X * Polynomial.C (U₁ i)
  let Simple : Finset I := Identity.filter fun i =>
    (BI i).derivative.eval (LI i) ≠ 0
  have hIdentity : 212479 ≤ Identity.card := by
    have hh : 212479 ≤ (Finset.univ.filter fun i : I ↦
        directAffineObstruction R (omega i) (U₀ i) (U₁ i) = 0).card := by
      omega
    simpa [Identity, G] using hh
  rcases large_simple_or_exists_sparse_nonsimple_coordinates_extended_6400
      Identity Simple (Finset.filter_subset _ _) hIdentity with
    hsimple | hrepeat
  · have hstrong :
        ∃ Good : Finset F, ∃ p₀ p₁ : F[X],
          Good ⊆ T ∧ 76781 < Good.card ∧
          p₀.natDegree ≤ 131071 ∧ p₁.natDegree ≤ 131071 ∧
          ∀ z ∈ Good, P z = p₀ + Polynomial.C z * p₁ := by
      apply simple_set_affine_owner_alignment_6400
        omega hn R D (by omega) (by omega)
        hYZ T P A U₀ U₁ Simple hsimple
      · intro i hi
        have hiIdentity := (Finset.mem_filter.mp hi).1
        have hGi : G i = 0 := (Finset.mem_filter.mp hiIdentity).2
        exact ⟨by simpa [G] using hGi, by simpa [BI, LI] using
          (Finset.mem_filter.mp hi).2⟩
      · exact hPdegree
      · intro z hz
        simpa only [← triEval_eq_eval_triSpecializeZ] using hvan z hz
      · exact hrow
      · exact hagreement
      · exact hT
      · exact hkF
    obtain ⟨Good, p₀, p₁, hGoodT, hGoodCard, hp₀, hp₁, hline⟩ := hstrong
    exact ⟨Good, p₀, p₁, hGoodT, by omega, hp₀, hp₁, hline⟩
  · obtain ⟨S, hSrepeat, hScard⟩ := hrepeat
    letI : Nonempty I :=
      ⟨(Finset.card_pos.mp (by omega : 0 < S.card)).choose⟩
    let W : Finset F := S.map omega
    let B : F → F[X][X] := fun x => triSpecializeX R x
    let line₀ : F → F := fun x => U₀ (Function.invFun omega x)
    let line₁ : F → F := fun x => U₁ (Function.invFun omega x)
    let L : F → F[X] := fun x =>
      Polynomial.C (line₀ x) + Polynomial.X * Polynomial.C (line₁ x)
    have hWcard : W.card = 131413 := by simpa [W] using hScard
    have hBne : ∀ x ∈ W, B x ≠ 0 := by
      intro x hx
      exact triSpecializeX_ne_zero_of_irreducible_natDegree_pos
        R hRirr (by omega) x
    have hBdeg : ∀ x ∈ W, (B x).natDegree ≤ 2 := by
      intro x hx
      exact (triSpecializeX_natDegree_le R x).trans hRdegree.le
    have hBXdeg : ∀ x ∈ W,
        Polynomial.Bivariate.degreeX (B x) ≤ D := by
      intro x hx
      have htotal : Polynomial.Bivariate.totalDegree (B x) ≤ D := by
        simpa [B, triSpecializeX, Polynomial.Bivariate.evalX_eq_map] using
          evalX_totalDegree_le_of_yzCap x R hYZ
      unfold Polynomial.Bivariate.degreeX
      apply Finset.sup_le
      intro i hi
      have hterm : ((B x).coeff i).natDegree + i ≤ D := by
        apply (Finset.le_sup
          (f := fun j => ((B x).coeff j).natDegree + j) hi).trans
        simpa [Polynomial.Bivariate.totalDegree] using htotal
      omega
    have hBroot : ∀ x ∈ W, (B x).eval (L x) = 0 := by
      intro x hx
      obtain ⟨i, hiS, hix⟩ := Finset.mem_map.mp hx
      subst x
      have hiIdentity : i ∈ Identity :=
        (Finset.mem_sdiff.mp (hSrepeat hiS)).1
      have hGi : G i = 0 := (Finset.mem_filter.mp hiIdentity).2
      change (triSpecializeX R (omega i)).eval
        (Polynomial.C (line₀ (omega i)) +
          Polynomial.X * Polynomial.C (line₁ (omega i))) = 0
      simpa [G, line₀, line₁,
        Function.leftInverse_invFun omega.injective i,
        directAffineObstruction, fixedAffineOwnerObstruction] using hGi
    have hBrepeated : ∀ x ∈ W, (B x).derivative.eval (L x) = 0 := by
      intro x hx
      obtain ⟨i, hiS, hix⟩ := Finset.mem_map.mp hx
      subst x
      have hiNotSimple : i ∉ Simple :=
        (Finset.mem_sdiff.mp (hSrepeat hiS)).2
      have hiIdentity : i ∈ Identity :=
        (Finset.mem_sdiff.mp (hSrepeat hiS)).1
      have hzero : (BI i).derivative.eval (LI i) = 0 := by
        by_contra hne
        exact hiNotSimple (Finset.mem_filter.mpr ⟨hiIdentity, hne⟩)
      simpa [B, L, BI, LI, line₀, line₁,
        Function.leftInverse_invFun omega.injective i] using hzero
    have hsectionRoot : ∀ z ∈ T, ∀ x ∈ W,
        ((B x).map (Polynomial.evalRingHom z)).eval ((P z).eval x) = 0 := by
      intro z hz x hx
      change biEval (triSpecializeX R x) ((P z).eval x) z = 0
      rw [← eval_triEval_eq_biEval_triSpecializeX, hvan z hz]
      simp
    apply factorYZ_repeated_quadratic_pencil_6400
      W T B L P line₀ line₁ D hWcard (by omega) hT hPdegree
    · intro x hx
      rfl
    · exact hBne
    · exact hBdeg
    · exact hBXdeg
    · exact hBroot
    · exact hBrepeated
    · exact hsectionRoot

end ProximityPrize.SubmissionLower
