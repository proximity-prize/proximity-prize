import ProximityPrize.SubmissionLower.BCHKSFactorYZIdentity6400

/-!
# Factor-specific linear closure at score 64.00

The high-identity degree-one branch needs to delete roots of only the linear
coefficient of each coordinate parent.  The selected factor's own `YZCap`
therefore supplies the cleanup degree directly.
-/

namespace ProximityPrize.SubmissionLower

open Polynomial
open RationalFunctions.HenselNumerators.ConcreteFiniteNumerators

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

variable {F : Type} [Field F]

/-- Sparse-dirty pencil assembly for linear coordinate parents, with an
arbitrary factor-specific cleanup cap. -/
theorem factorYZ_linear_sparse_dirty_pencil_6400
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
    (hBdeg : ∀ x ∈ W, (B x).natDegree ≤ 1)
    (hBXdeg : ∀ x ∈ W, Polynomial.Bivariate.degreeX (B x) ≤ D)
    (hBroot : ∀ x ∈ W, (B x).eval (L x) = 0)
    (hsectionRoot : ∀ z ∈ T, ∀ x ∈ W,
      ((B x).map (Polynomial.evalRingHom z)).eval
        ((sect z).eval x) = 0) :
    ∃ Good : Finset F, ∃ p₀ p₁ : F[X],
      Good ⊆ T ∧ 76780 < Good.card ∧
      p₀.natDegree ≤ 131071 ∧ p₁.natDegree ≤ 131071 ∧
      ∀ z ∈ Good, sect z = p₀ + Polynomial.C z * p₁ := by
  let G : F → F[X] := fun x ↦ (B x).coeff 1
  apply factorYZ_sparse_dirty_pencil_6400
    W T G sect line₀ line₁ D hWcard hD
  · intro x hx
    exact linearCoeff_ne_zero_of_root (B x) (L x)
      (hBne x hx) (hBdeg x hx) (hBroot x hx)
  · intro x hx
    exact (Polynomial.Bivariate.coeff_natDegree_le_degreeX (B x) 1).trans
      (hBXdeg x hx)
  · exact hT
  · exact hsectdeg
  · intro z hz x hx hclean
    have hquad : ((B x).coeff 2).eval z = 0 := by
      have hcoeff : (B x).coeff 2 = 0 :=
        Polynomial.coeff_eq_zero_of_natDegree_lt (by
          have := hBdeg x hx
          omega)
      simp [hcoeff]
    have hrootEq := degree_drop_linear_specialized_root_unique
      (B x) (L x) z ((sect z).eval x) (by
        exact (hBdeg x hx).trans (by omega))
      (hBroot x hx) hquad hclean (hsectionRoot z hz x hx)
    calc
      (sect z).eval x = (L x).eval z := hrootEq
      _ = line₀ x + z * line₁ x := by
        rw [hL x hx]
        simp only [Polynomial.eval_add, Polynomial.eval_C,
          Polynomial.eval_mul, Polynomial.eval_X]

/-- A high-identity irreducible degree-one selected factor forces the
score-64 pencil using its own additive `Y+Z` cap. -/
theorem fixed_factor_degree_one_high_identity_alignment_factorYZ6400
    {I F : Type} [Fintype I] [DecidableEq I]
    [Field F] [Fintype F] [DecidableEq F]
    (omega : I ↪ F) (hn : Fintype.card I = 262144)
    (R : F[X][X][X]) (hRirr : Irreducible R)
    (hRdegree : R.natDegree = 1)
    (D : ℕ) (hD : 0 < D) (hYZ : YZCap R D)
    (T : Finset F) (P : F → F[X]) (A : F → Finset I)
    (U₀ U₁ : I → F)
    (hPdegree : ∀ z ∈ T, (P z).natDegree ≤ 131071)
    (hvan : ∀ z ∈ T, triEval R z (P z) = 0)
    (hrow : ∀ z ∈ T, 185364 ≤ (A z).card)
    (hagreement : ∀ z ∈ T, ∀ i ∈ A z,
      (P z).eval (omega i) = U₀ i + z * U₁ i)
    (hT : 144802557 * D < T.card)
    (hhigh : 212478 < (Finset.univ.filter fun i : I ↦
      directAffineObstruction R (omega i) (U₀ i) (U₁ i) = 0).card) :
    ∃ Good : Finset F, ∃ p₀ p₁ : F[X],
      Good ⊆ T ∧ 76780 < Good.card ∧
      p₀.natDegree ≤ 131071 ∧ p₁.natDegree ≤ 131071 ∧
      ∀ z ∈ Good, P z = p₀ + Polynomial.C z * p₁ := by
  classical
  let G : I → F[X] := fun i =>
    directAffineObstruction R (omega i) (U₀ i) (U₁ i)
  let Identity : Finset I := Finset.univ.filter fun i => G i = 0
  have hIdentity : 212479 ≤ Identity.card := by
    have hh : 212479 ≤ (Finset.univ.filter fun i : I ↦
        directAffineObstruction R (omega i) (U₀ i) (U₁ i) = 0).card := by
      omega
    simpa [Identity, G] using hh
  obtain ⟨S, hSIdentity, hScard⟩ :=
    Finset.exists_subset_card_eq (show 131413 ≤ Identity.card by omega)
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
  have hBdeg : ∀ x ∈ W, (B x).natDegree ≤ 1 := by
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
    have hiIdentity := hSIdentity hiS
    have hGi : G i = 0 := (Finset.mem_filter.mp hiIdentity).2
    change (triSpecializeX R (omega i)).eval
      (Polynomial.C (line₀ (omega i)) +
        Polynomial.X * Polynomial.C (line₁ (omega i))) = 0
    simpa [G, line₀, line₁,
      Function.leftInverse_invFun omega.injective i,
      directAffineObstruction, fixedAffineOwnerObstruction] using hGi
  have hsectionRoot : ∀ z ∈ T, ∀ x ∈ W,
      ((B x).map (Polynomial.evalRingHom z)).eval ((P z).eval x) = 0 := by
    intro z hz x hx
    change biEval (triSpecializeX R x) ((P z).eval x) z = 0
    rw [← eval_triEval_eq_biEval_triSpecializeX, hvan z hz]
    simp
  apply factorYZ_linear_sparse_dirty_pencil_6400
    W T B L P line₀ line₁ D hWcard hD hT hPdegree
  · intro x hx
    rfl
  · exact hBne
  · exact hBdeg
  · exact hBXdeg
  · exact hBroot
  · exact hsectionRoot

/-- Complete selected-factor closure in outer degree one, combining the
factor-specific low- and high-identity branches. -/
theorem fixed_factor_degree_one_alignment_factorYZ6400
    {I F : Type} [Fintype I] [DecidableEq I]
    [Field F] [Fintype F] [DecidableEq F]
    (omega : I ↪ F) (hn : Fintype.card I = 262144)
    (R : F[X][X][X]) (hRirr : Irreducible R)
    (hRdegree : R.natDegree = 1)
    (D : ℕ) (hD : 0 < D) (hYZ : YZCap R D)
    (T : Finset F) (P : F → F[X]) (A : F → Finset I)
    (U₀ U₁ : I → F)
    (hPdegree : ∀ z ∈ T, (P z).natDegree ≤ 131071)
    (hvan : ∀ z ∈ T, triEval R z (P z) = 0)
    (hrow : ∀ z ∈ T, 185364 ≤ (A z).card)
    (hagreement : ∀ z ∈ T, ∀ i ∈ A z,
      (P z).eval (omega i) = U₀ i + z * U₁ i)
    (hT : 144802557 * D < T.card) :
    ∃ Good : Finset F, ∃ p₀ p₁ : F[X],
      Good ⊆ T ∧ 76780 < Good.card ∧
      p₀.natDegree ≤ 131071 ∧ p₁.natDegree ≤ 131071 ∧
      ∀ z ∈ Good, P z = p₀ + Polynomial.C z * p₁ := by
  by_cases hzhi : (Finset.univ.filter fun i : I ↦
      directAffineObstruction R (omega i) (U₀ i) (U₁ i) = 0).card ≤
        212478
  · exact fixed_factor_low_identity_alignment_factorYZ6400
      omega hn R D hD hYZ T P A U₀ U₁ hPdegree hvan hrow hagreement hT hzhi
  · apply fixed_factor_degree_one_high_identity_alignment_factorYZ6400
      omega hn R hRirr hRdegree D hD hYZ T P A U₀ U₁
      hPdegree hvan hrow hagreement hT
    omega

end ProximityPrize.SubmissionLower
