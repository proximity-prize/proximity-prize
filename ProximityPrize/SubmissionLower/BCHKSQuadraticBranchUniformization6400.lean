import ProximityPrize.SubmissionLower.BCHKSIdentitySparseRows6400
import ProximityPrize.SubmissionLower.BCHKSFixedObstructionUniformization6400

/-!
# Quadratic branch uniformization for the score-64 route

For a quadratic coordinate parent with a known affine root, the other-root
ambiguity is retained as an explicit linear residual factor.  A generic root
on that other branch can agree with the affine root only where the derivative
obstruction vanishes.  This is the quadratic analogue of retaining every
candidate in a finite algebraic moving frame instead of choosing a branch
prematurely.
-/

namespace ProximityPrize.SubmissionLower

open Polynomial Polynomial.Bivariate RationalFunctions
open RationalFunctions.HenselNumerators
open RationalFunctions.HenselNumerators.ConcreteFiniteNumerators
open scoped BigOperators

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

variable {F : Type} [Field F]

/-- The linear cofactor left after removing a known root `L` from a
polynomial of outer degree at most two. -/
noncomputable def quadraticResidual (B : F[X][X]) (L : F[X]) : F[X][X] :=
  Polynomial.C (B.coeff 2) * Polynomial.X +
    Polynomial.C (B.coeff 1 + B.coeff 2 * L)

/-- Explicit coefficient shape of a polynomial of degree at most two. -/
theorem eq_quadratic_coeff_shape (B : F[X][X]) (hdeg : B.natDegree ≤ 2) :
    B = Polynomial.C (B.coeff 0) +
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

/-- A second root of a quadratic with known root `L` is either that root or
is carried by the explicit linear residual factor. -/
theorem quadratic_root_eq_or_residual_root
    {K : Type} [Field K] (phi : F[X] →+* K)
    (B : F[X][X]) (L : F[X]) (y : K)
    (hdeg : B.natDegree ≤ 2)
    (hL : B.eval L = 0)
    (hy : (B.map phi).eval y = 0) :
    y = phi L ∨ ((quadraticResidual B L).map phi).eval y = 0 := by
  have hshape := eq_quadratic_coeff_shape B hdeg
  have hLy :
      phi (B.coeff 0) + phi (B.coeff 1) * phi L +
          phi (B.coeff 2) * (phi L) ^ 2 = 0 := by
    rw [hshape] at hL
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X, Polynomial.eval_pow] at hL
    simpa only [map_add, map_mul, map_pow, map_zero] using congrArg phi hL
  have hyy :
      phi (B.coeff 0) + phi (B.coeff 1) * y +
          phi (B.coeff 2) * y ^ 2 = 0 := by
    rw [hshape, Polynomial.map_add, Polynomial.map_add,
      Polynomial.map_mul, Polynomial.map_mul, Polynomial.map_pow,
      Polynomial.map_C, Polynomial.map_C, Polynomial.map_C,
      Polynomial.map_X] at hy
    simpa only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X, Polynomial.eval_pow] using hy
  have hfactor :
      (y - phi L) *
        (phi (B.coeff 2) * (y + phi L) + phi (B.coeff 1)) = 0 := by
    linear_combination hyy - hLy
  rcases mul_eq_zero.mp hfactor with heq | hres
  · exact Or.inl (sub_eq_zero.mp heq)
  · right
    simp only [quadraticResidual, Polynomial.map_add, Polynomial.map_mul,
      Polynomial.map_C, Polynomial.map_X, Polynomial.eval_add,
      Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X, map_add,
      map_mul]
    linear_combination hres

/-- Evaluating the residual on the known root gives the derivative there. -/
theorem quadraticResidual_eval_eq_derivative_eval
    (B : F[X][X]) (L : F[X]) (hdeg : B.natDegree ≤ 2) :
    (quadraticResidual B L).eval L = B.derivative.eval L := by
  have hshape := eq_quadratic_coeff_shape B hdeg
  have hderiv :
      B.derivative.eval L =
        B.coeff 1 + 2 * B.coeff 2 * L := by
    calc
      B.derivative.eval L =
          (Polynomial.C (B.coeff 0) +
            Polynomial.C (B.coeff 1) * Polynomial.X +
              Polynomial.C (B.coeff 2) * Polynomial.X ^ 2).derivative.eval L :=
        congrArg (fun Q : F[X][X] => Q.derivative.eval L) hshape
      _ = B.coeff 1 + 2 * B.coeff 2 * L := by
        simp only [Polynomial.derivative_add, Polynomial.derivative_mul,
          Polynomial.derivative_C, Polynomial.derivative_X,
          Polynomial.derivative_pow, Polynomial.eval_add,
          Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
          zero_mul, zero_add, mul_one]
        norm_num [Polynomial.eval_natCast]
        ring
  rw [hderiv]
  simp only [quadraticResidual, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X]
  ring

/-- A nonzero polynomial of degree at most two with a repeated known root has
a nonzero quadratic coefficient. -/
theorem coeff_two_ne_zero_of_quadratic_repeated_root
    (B : F[X][X]) (L : F[X])
    (hB : B ≠ 0) (hdeg : B.natDegree ≤ 2)
    (hroot : B.eval L = 0) (hderiv : B.derivative.eval L = 0) :
    B.coeff 2 ≠ 0 := by
  intro h2
  have hshape := eq_quadratic_coeff_shape B hdeg
  have hderiv' : B.coeff 1 + 2 * B.coeff 2 * L = 0 := by
    have hh := quadraticResidual_eval_eq_derivative_eval B L hdeg
    rw [hderiv] at hh
    simp only [quadraticResidual, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_X] at hh
    linear_combination hh
  have h1 : B.coeff 1 = 0 := by simpa [h2] using hderiv'
  have h0 : B.coeff 0 = 0 := by
    rw [hshape] at hroot
    simpa [h1, h2] using hroot
  apply hB
  rw [hshape, h0, h1, h2]
  simp

/-- Repeated-root uniqueness survives any coefficient embedding which keeps
nonzero coefficient polynomials nonzero. -/
theorem quadratic_repeated_root_unique_after_map
    {K : Type} [Field K] (phi : F[X] →+* K)
    (hinj : ∀ p : F[X], p ≠ 0 → phi p ≠ 0)
    (B : F[X][X]) (L : F[X]) (y : K)
    (hB : B ≠ 0) (hdeg : B.natDegree ≤ 2)
    (hL : B.eval L = 0) (hderiv : B.derivative.eval L = 0)
    (hy : (B.map phi).eval y = 0) :
    y = phi L := by
  rcases quadratic_root_eq_or_residual_root phi B L y hdeg hL hy with heq | hres
  · exact heq
  · have h2 : phi (B.coeff 2) ≠ 0 :=
      hinj (B.coeff 2)
        (coeff_two_ne_zero_of_quadratic_repeated_root
          B L hB hdeg hL hderiv)
    have hresL : ((quadraticResidual B L).map phi).eval (phi L) = 0 := by
      rw [Polynomial.eval_map_apply]
      rw [quadraticResidual_eval_eq_derivative_eval B L hdeg, hderiv, map_zero]
    have hres' :
        phi (B.coeff 2) * y + phi (B.coeff 1 + B.coeff 2 * L) = 0 := by
      simpa [quadraticResidual] using hres
    have hresL' :
        phi (B.coeff 2) * phi L +
            phi (B.coeff 1 + B.coeff 2 * L) = 0 := by
      simpa [quadraticResidual] using hresL
    have hzero : phi (B.coeff 2) * (y - phi L) = 0 := by
      linear_combination hres' - hresL'
    exact sub_eq_zero.mp ((mul_eq_zero.mp hzero).resolve_left h2)

/-- The derivative obstruction loses one unit of total `Y/Z` degree when the
known root is affine in `Z`. -/
theorem quadratic_derivative_affine_natDegree_le
    (B : F[X][X]) (L : F[X]) (D : ℕ)
    (hdeg : B.natDegree ≤ 2) (hLdeg : L.natDegree ≤ 1)
    (hD : 2 ≤ D) (htotal : Polynomial.Bivariate.totalDegree B ≤ D) :
    (B.derivative.eval L).natDegree ≤ D - 1 := by
  have hcoeff : ∀ i, i ≤ 2 → (B.coeff i).natDegree + i ≤ D := by
    intro i hi
    by_cases hz : B.coeff i = 0
    · simp [hz]
      omega
    · have his : i ∈ B.support := Polynomial.mem_support_iff.mpr hz
      exact (Finset.le_sup
        (f := fun j => (B.coeff j).natDegree + j) his).trans htotal
  have h1 := hcoeff 1 (by omega)
  have h2 := hcoeff 2 (by omega)
  have hshape := eq_quadratic_coeff_shape B hdeg
  have hderiv :
      B.derivative.eval L = B.coeff 1 + 2 * B.coeff 2 * L := by
    calc
      B.derivative.eval L =
          (Polynomial.C (B.coeff 0) +
            Polynomial.C (B.coeff 1) * Polynomial.X +
              Polynomial.C (B.coeff 2) * Polynomial.X ^ 2).derivative.eval L :=
        congrArg (fun Q : F[X][X] => Q.derivative.eval L) hshape
      _ = B.coeff 1 + 2 * B.coeff 2 * L := by
        simp only [Polynomial.derivative_add, Polynomial.derivative_mul,
          Polynomial.derivative_C, Polynomial.derivative_X,
          Polynomial.derivative_pow, Polynomial.eval_add,
          Polynomial.eval_mul, Polynomial.eval_C,
          zero_mul, zero_add, mul_one]
        norm_num [Polynomial.eval_natCast]
        ring
  rw [hderiv]
  apply (Polynomial.natDegree_add_le _ _).trans
  apply max_le
  · omega
  · calc
      (2 * B.coeff 2 * L).natDegree ≤
          (2 * B.coeff 2).natDegree + L.natDegree :=
        Polynomial.natDegree_mul_le
      _ ≤ (B.coeff 2).natDegree + L.natDegree := by
        gcongr
        have hmul : ((2 : F[X]) * B.coeff 2).natDegree ≤
            (2 : F[X]).natDegree + (B.coeff 2).natDegree :=
          Polynomial.natDegree_mul_le
        simpa using hmul
      _ ≤ (D - 2) + 1 := Nat.add_le_add (by omega) hLdeg
      _ ≤ D - 1 := by omega

/-- Coefficient specialization commutes with substituting a polynomial and
then specializing that polynomial. -/
theorem eval_map_eval_polynomial
    (A : F[X][X]) (L : F[X]) (z : F) :
    (A.map (Polynomial.evalRingHom z)).eval (L.eval z) =
      (A.eval L).eval z := by
  induction A using Polynomial.induction_on' with
  | add A B hA hB => simp [hA, hB]
  | monomial n a => simp [Polynomial.map_monomial, Polynomial.eval_monomial]

/-- If the function-field root takes the other quadratic branch, every good
specialization at which it equals the known affine root kills the derivative
obstruction. -/
theorem other_quadratic_branch_forces_derivative_zero
    [Fintype F] [DecidableEq F]
    {H : F[X][Y]} [Fact (Irreducible H)] [Fact (0 < H.natDegree)]
    (B : F[X][X]) (L : F[X])
    (y : 𝕃 H) (z : F) (root : rationalRoot (monicize H) z)
    (hdeg : B.natDegree ≤ 2) (hLroot : B.eval L = 0)
    (hyroot : (B.map (liftToFunctionField (H := H))).eval y = 0)
    (hother : y ≠ liftToFunctionField (H := H) L)
    (hgood : GoodAt z root y (L.eval z)) :
    (B.derivative.eval L).eval z = 0 := by
  have hresroot :
      ((quadraticResidual B L).map
        (liftToFunctionField (H := H))).eval y = 0 :=
    (quadratic_root_eq_or_residual_root
      (liftToFunctionField (H := H)) B L y hdeg hLroot hyroot).resolve_left hother
  have hspecialized := fixedOwner_specializes_root
    (H := H) (quadraticResidual B L) z root y (L.eval z) hgood hresroot
  have hresidual := congrArg (Polynomial.eval z)
    (quadraticResidual_eval_eq_derivative_eval B L hdeg)
  rw [← hresidual]
  rw [← eval_map_eval_polynomial]
  exact hspecialized

/-! ## Restricted incidence extraction -/

/-- If an agreement row misses at most `e` points of the ambient coordinate
set, it misses at most `e` points of every fixed subset. -/
theorem subset_filter_card_lower_of_row_bound
    {I : Type} [Fintype I] [DecidableEq I]
    (S A : Finset I) (n e : ℕ)
    (hn : Fintype.card I = n) (hA : n - e ≤ A.card) :
    S.card - e ≤ (S.filter fun i => i ∈ A).card := by
  let Missing : Finset I := S \ A
  have hmissingSub : Missing ⊆ Finset.univ \ A := by
    intro i hi
    simp only [Missing, Finset.mem_sdiff, Finset.mem_univ, true_and] at hi ⊢
    exact hi.2
  have hmissing : Missing.card ≤ e := by
    have hc := Finset.card_le_card hmissingSub
    have huniv : (Finset.univ \ A).card = n - A.card := by
      simp [Finset.card_sdiff, hn]
    rw [huniv] at hc
    omega
  have hsplit := Finset.card_sdiff_add_card_inter S A
  have hinter : S ∩ A = S.filter fun i => i ∈ A := by
    ext i
    simp
  rw [hinter] at hsplit
  change Missing.card + (S.filter fun i => i ∈ A).card = S.card at hsplit
  omega

/-- `many_large_fibers`, restricted to an arbitrary fixed coordinate subset.
This is the counting form needed for the simple quadratic locus. -/
theorem many_large_fibers_in_subset
    {I J : Type} [Fintype I] [DecidableEq I] [DecidableEq J]
    (S : Finset I) (T : Finset J) (A : J → Finset I)
    (n e k B : ℕ)
    (hn : Fintype.card I = n)
    (hrow : ∀ z ∈ T, n - e ≤ (A z).card)
    (hcount : (S.card - e - k) * T.card > (S.card - k) * B) :
    k + 1 ≤ (S.filter fun i =>
      B < (T.filter fun z => i ∈ A z).card).card := by
  classical
  let AS : J → Finset {i // i ∈ S} := fun z =>
    Finset.univ.filter fun i => (i : I) ∈ A z
  have hnS : Fintype.card {i // i ∈ S} = S.card := Fintype.card_coe S
  have hrowS : ∀ z ∈ T, S.card - e ≤ (AS z).card := by
    intro z hz
    have hh := subset_filter_card_lower_of_row_bound
      S (A z) n e hn (hrow z hz)
    let emb : {i // i ∈ S} ↪ I := Function.Embedding.subtype _
    have hmap : (AS z).map emb = S.filter fun i => i ∈ A z := by
      ext i
      simp [AS, emb, and_comm]
    rw [← hmap, Finset.card_map] at hh
    exact hh
  have hlarge := many_large_fibers T AS S.card e k B hnS hrowS hcount
  have hcardEq :
      (Finset.univ.filter fun i : {i // i ∈ S} =>
        B < (T.filter fun z => i ∈ AS z).card).card =
      (S.filter fun i => B < (T.filter fun z => i ∈ A z).card).card := by
    let emb : {i // i ∈ S} ↪ I := Function.Embedding.subtype _
    have hmap :
        (Finset.univ.filter fun i : {i // i ∈ S} =>
          B < (T.filter fun z => i ∈ AS z).card).map emb =
        S.filter fun i => B < (T.filter fun z => i ∈ A z).card := by
      ext i
      simp [AS, emb, and_comm]
    rw [← hmap, Finset.card_map]
  rw [← hcardEq]
  exact hlarge

/-- Score-64 arithmetic for the retained quadratic branches.  Nonsimple
identity coordinates are already exact; among the simple identity coordinates,
the incidence surplus supplies enough fibers larger than the derivative cap to
reach the interpolation dimension. -/
theorem score6400_many_quadratic_branch_coordinates
    {I F : Type} [Fintype I] [DecidableEq I]
    [Field F] [DecidableEq F]
    (Identity Simple : Finset I) (T : Finset F) (A : F → Finset I)
    (D : ℕ)
    (hn : Fintype.card I = 262144)
    (hSimple : Simple ⊆ Identity)
    (hIdentity : 212479 ≤ Identity.card)
    (hrow : ∀ z ∈ T, 185364 ≤ (A z).card)
    (hD : 2 ≤ D) (hT : 29 * D < T.card) :
    131072 ≤ ((Identity \ Simple) ∪
      (Simple.filter fun i =>
        D - 1 < (T.filter fun z => i ∈ A z).card)).card := by
  classical
  let Repeat : Finset I := Identity \ Simple
  let Good : Finset I := Simple.filter fun i =>
    D - 1 < (T.filter fun z => i ∈ A z).card
  have hsplit : Repeat.card + Simple.card = Identity.card := by
    have hh := Finset.card_sdiff_add_card_inter Identity Simple
    rw [Finset.inter_eq_right.mpr hSimple] at hh
    simpa [Repeat] using hh
  by_cases hrepeated : 131072 ≤ Repeat.card
  · exact hrepeated.trans (Finset.card_le_card (Finset.subset_union_left))
  · have hr : Repeat.card ≤ 131071 := by omega
    let k : ℕ := 131071 - Repeat.card
    have hIdentityUpper : Identity.card ≤ 262144 := by
      rw [← hn]
      exact Finset.card_le_univ Identity
    have hleft : 4628 ≤ Simple.card - 76780 - k := by
      dsimp [k]
      omega
    have hright : Simple.card - k ≤ 131073 := by
      dsimp [k]
      omega
    have hcount :
        (Simple.card - 76780 - k) * T.card >
          (Simple.card - k) * (D - 1) := by
      calc
        (Simple.card - 76780 - k) * T.card ≥ 4628 * T.card :=
          Nat.mul_le_mul_right T.card hleft
        _ > 4628 * (29 * D) :=
          Nat.mul_lt_mul_of_pos_left hT (by norm_num)
        _ > 131073 * D := by
          rw [← mul_assoc]
          exact Nat.mul_lt_mul_of_pos_right (by norm_num) (by omega)
        _ ≥ (Simple.card - k) * (D - 1) :=
          Nat.mul_le_mul hright (Nat.sub_le D 1)
    have hGood : k + 1 ≤ Good.card := by
      have hh := many_large_fibers_in_subset
        Simple T A 262144 76780 k (D - 1) hn hrow hcount
      simpa [Good] using hh
    have hdisjoint : Disjoint Repeat Good := by
      rw [Finset.disjoint_left]
      intro i hiR hiG
      have hiNot : i ∉ Simple := (Finset.mem_sdiff.mp hiR).2
      exact hiNot (Finset.mem_filter.mp hiG).1
    change 131072 ≤ (Repeat ∪ Good).card
    rw [Finset.card_union_of_disjoint hdisjoint]
    dsimp [k] at hGood
    omega

/-! ## Canonical-root uniformization -/

/-- In the high direct-identity branch of an irreducible quadratic selected
factor, retaining both quadratic branches supplies enough exact affine
coordinates to make the canonical function-field root globally affine in the
independent base coordinate. -/
theorem quadratic_branch_uniformizes_gamma_of_cap_6400
    {I F : Type} [Fintype I] [DecidableEq I]
    [Field F] [Fintype F] [DecidableEq F]
    {H : F[X][Y]} [Fact (Irreducible H)] [Fact (0 < H.natDegree)]
    (omega : I ↪ F) (hn : Fintype.card I = 262144)
    (x₀ : F) (R : F[X][X][Y]) (N : ℕ) (hN : 131071 ≤ N)
    (hRirr : Irreducible R) (hRdegree : R.natDegree = 2)
    (hHyp : HenselNumerators.Hypotheses x₀ R H)
    (hzeta : HenselNumerators.zeta R x₀ H ≠ 0)
    (D : ℕ) (hD : 2 ≤ D) (hYZ : YZCap R D)
    (hgammaRoot : (liftedR (R := R) (H := H)).eval
      (canonicalFunctionFieldGamma H x₀ R N 131071) = 0)
    (T : Finset F) (root : ∀ z : T, rationalRoot (monicize H) (z : F))
    (P : T → F[X]) (A : F → Finset I) (U₀ U₁ : I → F)
    (hPdeg : ∀ z : T, (P z).natDegree ≤ 131071)
    (hspecializes : ∀ z : T, ∀ i, i ≤ 131071 →
      concreteSpecializedAlpha x₀ R hHyp hzeta N (z : F) (root z) i =
        FiniteHensel.TaylorCoeff (P z) x₀ i)
    (hden : ∀ z : T, ∀ i, i ≤ 131071 →
      piZ (z : F) (root z) (concreteDenRegularBridge x₀ R hHyp i) ≠ 0)
    (hrow : ∀ z ∈ T, 185364 ≤ (A z).card)
    (hagree : ∀ z : T, ∀ i ∈ A (z : F),
      (P z).eval (omega i) = U₀ i + (z : F) * U₁ i)
    (hT : 29 * D < T.card)
    (hhigh : 212478 < (Finset.univ.filter fun i : I =>
      directAffineObstruction R (omega i) (U₀ i) (U₁ i) = 0).card) :
    ∃ p₀ p₁ : F[X], p₀.natDegree ≤ 131071 ∧
      p₁.natDegree ≤ 131071 ∧
      canonicalFunctionFieldGamma H x₀ R N 131071 =
        p₀.map (groundToFunctionField H) +
          Polynomial.C (liftToFunctionField (H := H) Polynomial.X) *
            p₁.map (groundToFunctionField H) := by
  classical
  let gamma : (𝕃 H)[X] := canonicalFunctionFieldGamma H x₀ R N 131071
  let B : I → F[X][X] := fun i => triSpecializeX R (omega i)
  let L : I → F[X] := fun i =>
    Polynomial.C (U₀ i) + Polynomial.X * Polynomial.C (U₁ i)
  let Identity : Finset I := Finset.univ.filter fun i =>
    directAffineObstruction R (omega i) (U₀ i) (U₁ i) = 0
  let Simple : Finset I := Identity.filter fun i =>
    (B i).derivative.eval (L i) ≠ 0
  let Repeat : Finset I := Identity \ Simple
  let Good : Finset I := Simple.filter fun i =>
    D - 1 < (T.filter fun z => i ∈ A z).card
  let Exact : Finset I := Repeat ∪ Good
  have hBne : ∀ i, B i ≠ 0 := by
    intro i
    exact triSpecializeX_ne_zero_of_irreducible_natDegree_pos
      R hRirr (by omega) (omega i)
  have hBdeg : ∀ i, (B i).natDegree ≤ 2 := by
    intro i
    exact (triSpecializeX_natDegree_le R (omega i)).trans hRdegree.le
  have hLdeg : ∀ i, (L i).natDegree ≤ 1 := by
    intro i
    dsimp [L]
    exact (Polynomial.natDegree_add_le _ _).trans
      (max_le (by simp) (Polynomial.natDegree_mul_le.trans (by simp)))
  have hBtotal : ∀ i, Polynomial.Bivariate.totalDegree (B i) ≤ D := by
    intro i
    simpa [B, triSpecializeX, Polynomial.Bivariate.evalX_eq_map] using
      evalX_totalDegree_le_of_yzCap (omega i) R hYZ
  have hcoordinateRoot : ∀ i,
      ((B i).map (liftToFunctionField (H := H))).eval
        (gamma.eval (fieldTo𝕃 (H := H) (omega i))) = 0 := by
    intro i
    exact coordinate_parent_carries_generic_root R gamma hgammaRoot (omega i)
  have hIdentityRoot : ∀ i ∈ Identity, (B i).eval (L i) = 0 := by
    intro i hi
    have hz := (Finset.mem_filter.mp hi).2
    simpa only [Identity, B, L, directAffineObstruction,
      fixedAffineOwnerObstruction] using hz
  have hSimpleSub : Simple ⊆ Identity := Finset.filter_subset _ _
  have hIdentityCard : 212479 ≤ Identity.card := by
    dsimp [Identity]
    omega
  have hExactCard : 131072 ≤ Exact.card := by
    have hh := score6400_many_quadratic_branch_coordinates
      Identity Simple T A D hn hSimpleSub hIdentityCard hrow hD hT
    simpa [Exact, Repeat, Good] using hh
  have hExactRoot : ∀ i ∈ Exact,
      gamma.eval (fieldTo𝕃 (H := H) (omega i)) =
        liftToFunctionField (H := H) (L i) := by
    intro i hi
    rcases Finset.mem_union.mp hi with hiRepeat | hiGood
    · have hiIdentity : i ∈ Identity := (Finset.mem_sdiff.mp hiRepeat).1
      have hiNotSimple : i ∉ Simple := (Finset.mem_sdiff.mp hiRepeat).2
      have hderiv : (B i).derivative.eval (L i) = 0 := by
        by_contra hne
        exact hiNotSimple (Finset.mem_filter.mpr ⟨hiIdentity, hne⟩)
      exact quadratic_repeated_root_unique_after_map
        (liftToFunctionField (H := H))
        (fun p hp => liftToFunctionField_ne_zero (H := H) hp)
        (B i) (L i) (gamma.eval (fieldTo𝕃 (H := H) (omega i)))
        (hBne i) (hBdeg i) (hIdentityRoot i hiIdentity) hderiv
        (hcoordinateRoot i)
    · have hiSimple : i ∈ Simple := (Finset.mem_filter.mp hiGood).1
      have hiLarge : D - 1 < (T.filter fun z => i ∈ A z).card :=
        (Finset.mem_filter.mp hiGood).2
      have hiIdentity : i ∈ Identity := hSimpleSub hiSimple
      have hderivNe : (B i).derivative.eval (L i) ≠ 0 :=
        (Finset.mem_filter.mp hiSimple).2
      by_contra hother
      have hsub : (T.filter fun z => i ∈ A z) ⊆
          ((B i).derivative.eval (L i)).roots.toFinset := by
        intro z hz
        have hzmem := Finset.mem_filter.mp hz
        let zT : T := ⟨z, hzmem.1⟩
        have hpoly := canonicalFunctionFieldGamma_polyGoodAt
          x₀ R hHyp hzeta N 131071 hN z (root zT) (P zT)
          (hPdeg zT) (hspecializes zT) (hden zT)
        have hgood := PolyGoodAt.eval₂_of_induction z (root zT)
          gamma (P zT) (fieldTo𝕃 (H := H) (omega i)) (omega i)
          (by simpa [gamma] using hpoly)
          (GoodAt.fieldTo𝕃 (H := H) z (root zT) (omega i))
        have hgood' : GoodAt z (root zT)
            (gamma.eval (fieldTo𝕃 (H := H) (omega i))) ((L i).eval z) := by
          have ha := hagree zT i hzmem.2
          have hLeval : (L i).eval z = U₀ i + z * U₁ i := by
            change (Polynomial.C (U₀ i) +
              Polynomial.X * Polynomial.C (U₁ i)).eval z = _
            rw [Polynomial.eval_add, Polynomial.eval_mul,
              Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_C]
          rw [hLeval, ← ha]
          exact hgood
        have hzero := other_quadratic_branch_forces_derivative_zero
          (H := H) (B i) (L i)
          (gamma.eval (fieldTo𝕃 (H := H) (omega i))) z (root zT)
          (hBdeg i) (hIdentityRoot i hiIdentity) (hcoordinateRoot i)
          hother hgood'
        rw [Multiset.mem_toFinset, Polynomial.mem_roots hderivNe]
        exact hzero
      have hdegree : ((B i).derivative.eval (L i)).natDegree ≤ D - 1 :=
        quadratic_derivative_affine_natDegree_le
          (B i) (L i) D (hBdeg i) (hLdeg i) hD (hBtotal i)
      have hcard : (T.filter fun z => i ∈ A z).card ≤ D - 1 := by
        calc
          (T.filter fun z => i ∈ A z).card ≤
              ((B i).derivative.eval (L i)).roots.toFinset.card :=
            Finset.card_le_card hsub
          _ ≤ ((B i).derivative.eval (L i)).roots.card :=
            Multiset.toFinset_card_le _
          _ ≤ ((B i).derivative.eval (L i)).natDegree :=
            Polynomial.card_roots' _
          _ ≤ D - 1 := hdegree
      exact (not_lt_of_ge hcard) hiLarge
  let Dfield : Finset F := Exact.map omega
  have hDfieldCard : 131072 ≤ Dfield.card := by
    simpa [Dfield] using hExactCard
  haveI : Nonempty I := Fintype.card_pos_iff.mp (by rw [hn]; norm_num)
  let U₀f : F → F := fun x => U₀ (Function.invFun omega x)
  let U₁f : F → F := fun x => U₁ (Function.invFun omega x)
  have heval : ∀ x ∈ Dfield,
      gamma.eval (fieldTo𝕃 (H := H) x) =
        fieldTo𝕃 (H := H) (U₀f x) +
          liftToFunctionField (H := H) Polynomial.X *
            fieldTo𝕃 (H := H) (U₁f x) := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hx
    have hh := hExactRoot i hi
    rw [hh]
    simp only [U₀f, U₁f, Function.leftInverse_invFun omega.injective i]
    change liftToFunctionField (H := H) (L i) =
      liftToFunctionField (H := H) (Polynomial.C (U₀ i)) +
        liftToFunctionField (H := H) Polynomial.X *
          liftToFunctionField (H := H) (Polynomial.C (U₁ i))
    rw [show L i = Polynomial.C (U₀ i) +
      Polynomial.X * Polynomial.C (U₁ i) by rfl, map_add, map_mul]
  exact canonicalFunctionFieldGamma_baseZ_affine
    x₀ R N 131071 Dfield hDfieldCard U₀f U₁f
    (canonicalFunctionFieldGamma_natDegree_le x₀ R N 131071)
    (by simpa [gamma] using heval)

/-- Complete selected-pair consumer for the high-identity quadratic branch. -/
theorem quadratic_branch_selected_pair_alignment_of_cap_6400
    {I F : Type} [Fintype I] [DecidableEq I]
    [Field F] [Fintype F] [DecidableEq F]
    {H : F[X][Y]} [Fact (Irreducible H)] [Fact (0 < H.natDegree)]
    (omega : I ↪ F) (hn : Fintype.card I = 262144)
    (x₀ : F) (R : F[X][X][Y]) (N : ℕ) (hN : 131071 ≤ N)
    (hRirr : Irreducible R) (hRdegree : R.natDegree = 2)
    (hHyp : HenselNumerators.Hypotheses x₀ R H)
    (hzeta : HenselNumerators.zeta R x₀ H ≠ 0)
    (D : ℕ) (hD : 2 ≤ D) (hYZ : YZCap R D)
    (hgammaRoot : (liftedR (R := R) (H := H)).eval
      (canonicalFunctionFieldGamma H x₀ R N 131071) = 0)
    (T : Finset F) (root : ∀ z : T, rationalRoot (monicize H) (z : F))
    (P : T → F[X]) (A : F → Finset I) (U₀ U₁ : I → F)
    (hPdeg : ∀ z : T, (P z).natDegree ≤ 131071)
    (hspecializes : ∀ z : T, ∀ i, i ≤ 131071 →
      concreteSpecializedAlpha x₀ R hHyp hzeta N (z : F) (root z) i =
        FiniteHensel.TaylorCoeff (P z) x₀ i)
    (hden : ∀ z : T, ∀ i, i ≤ 131071 →
      piZ (z : F) (root z) (concreteDenRegularBridge x₀ R hHyp i) ≠ 0)
    (hrow : ∀ z ∈ T, 185364 ≤ (A z).card)
    (hagree : ∀ z : T, ∀ i ∈ A (z : F),
      (P z).eval (omega i) = U₀ i + (z : F) * U₁ i)
    (hT : 29 * D < T.card)
    (hhigh : 212478 < (Finset.univ.filter fun i : I =>
      directAffineObstruction R (omega i) (U₀ i) (U₁ i) = 0).card)
    (hkF : 131071 < Fintype.card F) :
    ∃ p₀ p₁ : F[X], p₀.natDegree ≤ 131071 ∧
      p₁.natDegree ≤ 131071 ∧
      ∀ z : T, P z = p₀ + Polynomial.C (z : F) * p₁ := by
  obtain ⟨p₀, p₁, hp₀, hp₁, hgamma⟩ :=
    quadratic_branch_uniformizes_gamma_of_cap_6400
      omega hn x₀ R N hN hRirr hRdegree hHyp hzeta D hD hYZ
      hgammaRoot T root P A U₀ U₁ hPdeg hspecializes hden hrow hagree hT hhigh
  exact ⟨p₀, p₁, hp₀, hp₁,
    selected_polynomials_align_of_canonical_gamma_baseZ_affine
      x₀ R hHyp hzeta N 131071 hN T root P hPdeg hspecializes hden
      hkF p₀ p₁ hp₀ hp₁ hgamma⟩

/-- Score-data form: exact generic-root status is discharged internally from
middle Hensel vanishing and the selected factor's weighted support cap. -/
theorem quadratic_branch_selected_pair_alignment_of_score_data_6400
    {I F : Type} [Fintype I] [DecidableEq I]
    [Field F] [Fintype F] [DecidableEq F]
    {H : F[X][Y]} [Fact (Irreducible H)] [Fact (0 < H.natDegree)]
    (omega : I ↪ F) (hn : Fintype.card I = 262144)
    (x₀ : F) (R : F[X][X][Y]) (N : ℕ) (hN : 131071 ≤ N)
    (hRirr : Irreducible R) (hRdegree : R.natDegree = 2)
    (hHyp : HenselNumerators.Hypotheses x₀ R H)
    (hzeta : HenselNumerators.zeta R x₀ H ≠ 0)
    (D : ℕ) (hD : 2 ≤ D) (hYZ : YZCap R D)
    (hmiddle : ∀ t, 131071 < t → t < N →
      finiteAlpha (R := R) (H := H) x₀ N t = 0)
    (hweighted : ∀ j a, (R.coeff j).coeff a ≠ 0 →
      a + 131071 * j < N)
    (T : Finset F) (root : ∀ z : T, rationalRoot (monicize H) (z : F))
    (P : T → F[X]) (A : F → Finset I) (U₀ U₁ : I → F)
    (hPdeg : ∀ z : T, (P z).natDegree ≤ 131071)
    (hspecializes : ∀ z : T, ∀ i, i ≤ 131071 →
      concreteSpecializedAlpha x₀ R hHyp hzeta N (z : F) (root z) i =
        FiniteHensel.TaylorCoeff (P z) x₀ i)
    (hden : ∀ z : T, ∀ i, i ≤ 131071 →
      piZ (z : F) (root z) (concreteDenRegularBridge x₀ R hHyp i) ≠ 0)
    (hrow : ∀ z ∈ T, 185364 ≤ (A z).card)
    (hagree : ∀ z : T, ∀ i ∈ A (z : F),
      (P z).eval (omega i) = U₀ i + (z : F) * U₁ i)
    (hT : 29 * D < T.card)
    (hhigh : 212478 < (Finset.univ.filter fun i : I =>
      directAffineObstruction R (omega i) (U₀ i) (U₁ i) = 0).card)
    (hkF : 131071 < Fintype.card F) :
    ∃ p₀ p₁ : F[X], p₀.natDegree ≤ 131071 ∧
      p₁.natDegree ≤ 131071 ∧
      ∀ z : T, P z = p₀ + Polynomial.C (z : F) * p₁ := by
  have hroot := canonicalFunctionFieldGamma_is_root_of_score_data
    x₀ R hHyp hzeta N 131071 hN (by omega) hmiddle hweighted
  exact quadratic_branch_selected_pair_alignment_of_cap_6400
    omega hn x₀ R N hN hRirr hRdegree hHyp hzeta D hD hYZ hroot
    T root P A U₀ U₁ hPdeg hspecializes hden hrow hagree hT hhigh hkF

end ProximityPrize.SubmissionLower
