import ProximityPrize.SubmissionLower.BCHKSIdentitySparseRows6400

/-!
# Cross-branch uniformization for the score-64 fixed-factor route

At a direct-identity coordinate, the received affine graph is a linear
irreducible child of the specialized parent.  The lemmas below construct a
cleanup polynomial that excludes disappearing specializations and collisions
between distinct children.  This deliberately does *not* claim that a section
root must lie on the affine child: a section may instead choose a distinct
child with a distinct root.  Resolving that remaining ambiguity requires a
separate global-consistency argument.

This is the finite-branch analogue of retaining every candidate left by a
stabilizer and resolving the ambiguity by global consistency.
-/

namespace ProximityPrize.SubmissionLower

open Polynomial Polynomial.Bivariate
open RationalFunctions.HenselNumerators.ConcreteFiniteNumerators

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- A polynomial root is carried by a positive normalized child.  Constant
coefficient factors cannot vanish under polynomial substitution. -/
theorem exists_positiveChild_eval_eq_zero
    (B : F[X][Y]) (hB : B ≠ 0) (L : F[X]) (hroot : B.eval L = 0) :
    ∃ J ∈ positiveChildren B, J.eval L = 0 := by
  let phi : F[X][Y] →+* F[X] := Polynomial.evalRingHom L
  have hphi : phi B = 0 := by simpa [phi] using hroot
  obtain ⟨J, hJB, hJzero⟩ :=
    exists_normalizedFactor_map_eq_zero (Q := B) phi hB hphi
  have hpos : 0 < J.natDegree := by
    apply Nat.pos_of_ne_zero
    intro hdeg
    obtain ⟨c, hc⟩ := Polynomial.natDegree_eq_zero.mp hdeg
    have hJc : J = Polynomial.C c := hc.symm
    have hc0 : c = 0 := by
      rw [hJc] at hJzero
      simpa [phi] using hJzero
    have hJ0 : J = 0 := by rw [hJc, hc0]; simp
    exact (UniqueFactorizationMonoid.prime_of_normalized_factor J hJB).ne_zero hJ0
  exact ⟨J, mem_positiveChildren_iff.mpr ⟨hJB, hpos⟩, by simpa [phi] using hJzero⟩

/-- A specialized root of the same positive child as an affine polynomial
identity equals the affine value. -/
theorem specialized_root_eq_affine_of_affineIdentityOwner
    (B J : F[X][Y]) (a b z y : F)
    (hJ : J ∈ positiveChildren B)
    (hidentity :
      J.eval (Polynomial.C a + Polynomial.X * Polynomial.C b) = 0)
    (hroot : (J.map (Polynomial.evalRingHom z)).eval y = 0) :
    y = a + z * b := by
  let L : F[X][Y] :=
    Polynomial.X - Polynomial.C
      (Polynomial.C a + Polynomial.X * Polynomial.C b)
  have hassoc : Associated J L := by
    simpa [L] using
      positiveChild_affineIdentity_associated_linear_lift B J a b hJ hidentity
  obtain ⟨C, hLC⟩ := hassoc.dvd
  have hrootL : (L.map (Polynomial.evalRingHom z)).eval y = 0 := by
    rw [hLC, Polynomial.map_mul, Polynomial.eval_mul, hroot, zero_mul]
  have hplain : y - (a + b * z) = 0 := by
    simpa [L] using hrootL
  calc
    y = a + b * z := sub_eq_zero.mp hplain
    _ = a + z * b := by ring

/-- The cleanup polynomial for one coordinate parent.  Its leading
coefficient removes disappearing specializations; its remaining factors
remove every cross-child collision. -/
noncomputable def crossBranchCleanup (B : F[X][Y]) : F[X] :=
  B.leadingCoeff *
    ∏ z ∈ crossChildChallenges B, (Polynomial.X - Polynomial.C z)

theorem crossBranchCleanup_ne_zero
    (B : F[X][Y]) (hB : B ≠ 0) : crossBranchCleanup B ≠ 0 := by
  classical
  apply mul_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr hB)
  apply Finset.prod_ne_zero_iff.mpr
  intro z hz
  exact Polynomial.X_sub_C_ne_zero z

theorem crossBranchCleanup_natDegree_le
    (B : F[X][Y]) (hB : B ≠ 0) (d D : ℕ)
    (hY : B.natDegree ≤ d) (hZ : Bivariate.degreeX B ≤ D) :
    (crossBranchCleanup B).natDegree ≤ (d + 1) * D := by
  classical
  have hlead : B.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hB
  have hprod :
      (∏ z ∈ crossChildChallenges B,
        (Polynomial.X - Polynomial.C z : F[X])) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro z hz
    exact Polynomial.X_sub_C_ne_zero z
  have hleadDegree : B.leadingCoeff.natDegree ≤ D := by
    exact (Bivariate.coeff_natDegree_le_degreeX B B.natDegree).trans hZ
  have hcross : (crossChildChallenges B).card ≤ d * D :=
    crossChildChallenges_card_le_mul B hB d D hY hZ
  unfold crossBranchCleanup
  rw [Polynomial.natDegree_mul hlead hprod,
    Polynomial.natDegree_finsetProd_X_sub_C_eq_card]
  calc
    B.leadingCoeff.natDegree + (crossChildChallenges B).card
        ≤ D + d * D := Nat.add_le_add hleadDegree hcross
    _ = (d + 1) * D := by ring

/-- Nonvanishing of the cleanup simultaneously preserves the parent and
excludes every cross-child collision. -/
theorem crossBranchCleanup_clean
    (B : F[X][Y]) (z : F)
    (hclean : (crossBranchCleanup B).eval z ≠ 0) :
    biSpecializeZ B z ≠ 0 ∧ z ∉ crossChildChallenges B := by
  classical
  have hmul :
      B.leadingCoeff.eval z *
        (∏ w ∈ crossChildChallenges B,
          (Polynomial.X - Polynomial.C w : F[X])).eval z ≠ 0 := by
    simpa [crossBranchCleanup, Polynomial.eval_mul] using hclean
  have hlead : B.leadingCoeff.eval z ≠ 0 :=
    (mul_ne_zero_iff.mp hmul).1
  constructor
  · intro hzero
    have hc := congrArg (fun p : F[X] ↦ p.coeff B.natDegree) hzero
    apply hlead
    simpa [biSpecializeZ, Polynomial.coeff_map] using hc
  · intro hcross
    have hprodZero :
        (∏ w ∈ crossChildChallenges B,
          (Polynomial.X - Polynomial.C w : F[X])).eval z = 0 := by
      rw [Polynomial.eval_prod]
      apply Finset.prod_eq_zero hcross
      simp
    exact hmul (by rw [hprodZero, mul_zero])

/-- Exact arithmetic converting the selected fixed-factor fiber and the
degree-`(d+1)D` cleanup charge into more than `76781` clean rows. -/
theorem crossBranch_score6400_clean_rows_numeric
    (tcard bad good d : ℕ)
    (hd : 2 ≤ d)
    (hT : 2266 * 1898945373 * d < tcard)
    (hpart : good + bad = tcard)
    (hbad : 114 * bad ≤ 131413 * ((d + 1) * 1898945373)) :
    76781 < good := by
  norm_num at hT hbad ⊢
  nlinarith

/- Rejected route, retained as an audit trail: the proof below tried to infer
that a section root and the affine-child root were a *common* root of two
children.  They can instead be distinct roots, so the required routing premise
is unavailable.  Do not revive this theorem without a genuine global branch
selection argument.

/-- High direct-identity coordinates close every selected-factor degree at
least two.  Cross-child resultants retain all local branch candidates, while
global sparse-row consistency selects the affine child. -/
theorem fixed_factor_high_identity_alignment_6400
    (R : F[X][X][Y]) (hRirr : Irreducible R)
    (hRdegree : 2 ≤ R.natDegree)
    (hYZ : YZCap R 1898945373)
    (T W : Finset F) (P : F → F[X]) (line₀ line₁ : F → F)
    (hWcard : W.card = 131413)
    (hPdegree : ∀ z ∈ T, (P z).natDegree ≤ 131071)
    (hvan : ∀ z ∈ T, triEval R z (P z) = 0)
    (hidentity : ∀ x ∈ W,
      (triSpecializeX R x).eval
        (Polynomial.C (line₀ x) + Polynomial.X * Polynomial.C (line₁ x)) = 0)
    (hT : 2266 * 1898945373 * R.natDegree < T.card) :
    ∃ Good : Finset F, ∃ p₀ p₁ : F[X],
      Good ⊆ T ∧ 76781 < Good.card ∧
      p₀.natDegree ≤ 131071 ∧ p₁.natDegree ≤ 131071 ∧
      ∀ z ∈ Good, P z = p₀ + Polynomial.C z * p₁ := by
  classical
  let B : F → F[X][Y] := fun x ↦ triSpecializeX R x
  let G : F → F[X] := fun x ↦ crossBranchCleanup (B x)
  let Bad : F → Finset F := fun z ↦ W.filter fun x ↦ (G x).eval z = 0
  let Good : Finset F := T.filter fun z ↦ (Bad z).card ≤ 113
  have hBne : ∀ x ∈ W, B x ≠ 0 := by
    intro x hx
    exact triSpecializeX_ne_zero_of_irreducible_natDegree_pos
      R hRirr (by omega) x
  have hBY : ∀ x ∈ W, (B x).natDegree ≤ R.natDegree := by
    intro x hx
    exact triSpecializeX_natDegree_le R x
  have hBX : ∀ x ∈ W, Bivariate.degreeX (B x) ≤ 1898945373 := by
    intro x hx
    have htotal : Bivariate.totalDegree (B x) ≤ 1898945373 := by
      simpa [B, triSpecializeX, Bivariate.evalX_eq_map] using
        evalX_totalDegree_le_of_yzCap x R hYZ
    unfold Bivariate.degreeX
    apply Finset.sup_le
    intro i hi
    have hterm : ((B x).coeff i).natDegree + i ≤ 1898945373 := by
      apply (Finset.le_sup
        (f := fun j ↦ ((B x).coeff j).natDegree + j) hi).trans
      simpa [Bivariate.totalDegree] using htotal
    omega
  have hGne : ∀ x ∈ W, G x ≠ 0 := by
    intro x hx
    exact crossBranchCleanup_ne_zero (B x) (hBne x hx)
  have hGdegree : ∀ x ∈ W,
      (G x).natDegree ≤ (R.natDegree + 1) * 1898945373 := by
    intro x hx
    exact crossBranchCleanup_natDegree_le (B x) (hBne x hx)
      R.natDegree 1898945373 (hBY x hx) (hBX x hx)
  have hbadCount :
      114 * (T.filter fun z ↦ 113 < (Bad z).card).card ≤
        W.card * ((R.natDegree + 1) * 1898945373) := by
    simpa [Bad] using sparse_bad_seed_count W T G
      ((R.natDegree + 1) * 1898945373) 113 hGne hGdegree
  have hpart : Good.card +
      (T.filter fun z ↦ 113 < (Bad z).card).card = T.card := by
    simpa only [Good, not_le] using
      (Finset.card_filter_add_card_filter_not
        (s := T) (p := fun z ↦ (Bad z).card ≤ 113))
  have hGoodCard : 76781 < Good.card := by
    apply crossBranch_score6400_clean_rows_numeric T.card
      (T.filter fun z ↦ 113 < (Bad z).card).card Good.card R.natDegree
      hRdegree hT hpart
    simpa [hWcard] using hbadCount
  have hcleanAgreement : ∀ z ∈ Good, ∀ x ∈ W \ Bad z,
      (P z).eval x = line₀ x + z * line₁ x := by
    intro z hz x hx
    have hzT : z ∈ T := (Finset.mem_filter.mp hz).1
    have hxW := (Finset.mem_sdiff.mp hx).1
    have hGclean : (G x).eval z ≠ 0 := by
      intro hzero
      exact (Finset.mem_sdiff.mp hx).2
        (Finset.mem_filter.mpr ⟨hxW, hzero⟩)
    apply section_root_eq_affine_of_crossBranchCleanup
      (B x) (hBne x hxW) (line₀ x) (line₁ x) z ((P z).eval x)
    · simpa [B] using hidentity x hxW
    · change biEval (triSpecializeX R x) ((P z).eval x) z = 0
      rw [← eval_triEval_eq_biEval_triSpecializeX, hvan z hzT]
      simp
    · simpa [G] using hGclean
  have htwo : 1 < Good.card := by omega
  obtain ⟨z₀, hz₀, z₁, hz₁, hzne⟩ := Finset.one_lt_card.mp htwo
  obtain ⟨p₀, p₁, hp₀, hp₁, hpencil⟩ :=
    sparseBad_pencil_alignment_6400 Good W P line₀ line₁ Bad hWcard
      (fun z hz ↦ hPdegree z (Finset.mem_filter.mp hz).1)
      (fun z hz ↦ (Finset.mem_filter.mp hz).2)
      hcleanAgreement hz₀ hz₁ hzne
  exact ⟨Good, p₀, p₁, Finset.filter_subset _ _, hGoodCard,
    hp₀, hp₁, fun z hz ↦ hpencil z hz⟩
-/

end ProximityPrize.SubmissionLower
