import ProximityPrize.SubmissionLower.BCHKSFixedObstructionIncidence6400

namespace ProximityPrize.SubmissionLower

open Polynomial Polynomial.Bivariate RationalFunctions
open RationalFunctions.HenselNumerators
open RationalFunctions.HenselNumerators.ConcreteFiniteNumerators

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

/-- An irreducible relation of positive outer degree cannot vanish identically
after fixing the `X` coordinate.  Otherwise `X-x` divides every outer
coefficient and hence the whole relation, contradicting irreducibility and
positive outer degree. -/
theorem triSpecializeX_ne_zero_of_irreducible_natDegree_pos
    {F : Type} [Field F]
    (R : F[X][X][Y]) (hR : Irreducible R)
    (hpos : 0 < R.natDegree) (x : F) :
    triSpecializeX R x ≠ 0 := by
  intro hzero
  let L : F[X][X] := Polynomial.X - Polynomial.C (Polynomial.C x)
  have hcoeff : ∀ j, L ∣ R.coeff j := by
    intro j
    rw [Polynomial.dvd_iff_isRoot]
    change (R.coeff j).eval (Polynomial.C x) = 0
    have hj := congrArg (fun p : F[X][Y] => p.coeff j) hzero
    simpa [triSpecializeX, Polynomial.coeff_map] using hj
  have hCdvd : Polynomial.C L ∣ R :=
    (Polynomial.C_dvd_iff_dvd_coeff L R).mpr hcoeff
  rcases (hR.dvd_iff.mp hCdvd) with hunit | hassoc
  · have hLunit : IsUnit L := Polynomial.isUnit_C.mp hunit
    exact Polynomial.not_isUnit_X_sub_C (Polynomial.C x) hLunit
  · have hRdvd : R ∣ Polynomial.C L := hassoc.dvd
    have hL0 : L ≠ 0 := Polynomial.X_sub_C_ne_zero (Polynomial.C x)
    have hCL0 : Polynomial.C L ≠ 0 := Polynomial.C_ne_zero.mpr hL0
    have hdeg := Polynomial.natDegree_le_of_dvd hRdvd hCL0
    rw [Polynomial.natDegree_C] at hdeg
    omega

/-- Evaluating the mapped relation in the base coordinate commutes with first
specializing that coordinate in the original trivariate relation. -/
theorem liftedR_eval_at_coordinate
    {F : Type} [Field F]
    {H : F[X][Y]} [Fact (Irreducible H)] [Fact (0 < H.natDegree)]
    (R : F[X][X][Y]) (gamma : (𝕃 H)[X]) (x : F) :
    ((liftedR (R := R) (H := H)).eval gamma).eval
        (fieldTo𝕃 (H := H) x) =
      ((triSpecializeX R x).map (liftToFunctionField (H := H))).eval
        (gamma.eval (fieldTo𝕃 (H := H) x)) := by
  unfold liftedR triSpecializeX fieldTo𝕃
  induction R using Polynomial.induction_on' with
  | add A B hA hB =>
      simp only [Polynomial.map_add, Polynomial.eval_add]
      rw [hA, hB]
  | monomial n A =>
      simp [Polynomial.map_monomial, Polynomial.eval_monomial,
        eval_map_eval_eq_eval_eval_C]

/-- An exact generic relation root specializes to an exact root of every
nonzero coordinate parent. -/
theorem coordinate_parent_carries_generic_root
    {F : Type} [Field F]
    {H : F[X][Y]} [Fact (Irreducible H)] [Fact (0 < H.natDegree)]
    (R : F[X][X][Y]) (gamma : (𝕃 H)[X])
    (hroot : (liftedR (R := R) (H := H)).eval gamma = 0) (x : F) :
    ((triSpecializeX R x).map (liftToFunctionField (H := H))).eval
        (gamma.eval (fieldTo𝕃 (H := H) x)) = 0 := by
  have heval := congrArg
    (fun p : (𝕃 H)[X] => p.eval (fieldTo𝕃 (H := H) x)) hroot
  rw [liftedR_eval_at_coordinate R gamma x] at heval
  simpa using heval

/-- Affine substitution into a bivariate polynomial has univariate degree at
most its total degree. -/
theorem natDegree_fixedAffineOwnerObstruction_le_totalDegree
    {F : Type} [Field F] (J : F[X][Y]) (a b : F) :
    (fixedAffineOwnerObstruction J a b).natDegree ≤
      Polynomial.Bivariate.totalDegree J := by
  classical
  unfold fixedAffineOwnerObstruction
  rw [Polynomial.eval_eq_sum_range]
  apply (Polynomial.natDegree_sum_le _ _).trans
  rw [Finset.fold_max_le]
  constructor
  · exact Nat.zero_le _
  intro i hi
  simp only [Function.comp_apply]
  have haff :
      (Polynomial.C a + Polynomial.X * Polynomial.C b : F[X]).natDegree ≤ 1 :=
    (Polynomial.natDegree_add_le _ _).trans
      (max_le (by simp) (Polynomial.natDegree_mul_le.trans (by simp)))
  have hpow :
      ((Polynomial.C a + Polynomial.X * Polynomial.C b : F[X]) ^ i).natDegree ≤ i := by
    calc
      _ ≤ i * (Polynomial.C a + Polynomial.X * Polynomial.C b : F[X]).natDegree :=
        Polynomial.natDegree_pow_le
      _ ≤ i * 1 := Nat.mul_le_mul_left i haff
      _ = i := by omega
  by_cases hc : J.coeff i = 0
  · simp [hc]
  · have his : i ∈ J.support := Polynomial.mem_support_iff.mpr hc
    exact Polynomial.natDegree_mul_le.trans
      ((Nat.add_le_add_left hpow _).trans (by
        simpa [Nat.add_comm] using Polynomial.Bivariate.coeff_totalDegree_le J his))

/-- A positive normalized child cannot have larger total degree than its
nonzero parent. -/
theorem positiveChild_totalDegree_le
    {F : Type} [Field F] [DecidableEq F] (B J : F[X][Y])
    (hB : B ≠ 0) (hJ : J ∈ positiveChildren B) :
    Polynomial.Bivariate.totalDegree J ≤
      Polynomial.Bivariate.totalDegree B := by
  have hnorm := (mem_positiveChildren_iff.mp hJ).1
  have hJ0 : J ≠ 0 :=
    (UniqueFactorizationMonoid.prime_of_normalized_factor J hnorm).ne_zero
  have hdvd : J ∣ B :=
    UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hnorm
  obtain ⟨C, rfl⟩ := hdvd
  have hC0 : C ≠ 0 := by
    intro hC
    apply hB
    simp [hC]
  rw [Polynomial.Bivariate.totalDegree_mul hJ0 hC0]
  exact Nat.le_add_right _ _

/-- Complete degree ledger for a fixed affine owner obstruction. -/
theorem fixedAffineOwnerObstruction_degree_le_of_yzCap
    {F : Type} [Field F] [DecidableEq F]
    (R : F[X][X][Y]) (x a b : F) (J : F[X][Y]) (D : ℕ)
    (hB : triSpecializeX R x ≠ 0)
    (hJ : J ∈ positiveChildren (triSpecializeX R x))
    (hYZ : YZCap R D) :
    (fixedAffineOwnerObstruction J a b).natDegree ≤ D := by
  calc
    _ ≤ Polynomial.Bivariate.totalDegree J :=
      natDegree_fixedAffineOwnerObstruction_le_totalDegree J a b
    _ ≤ Polynomial.Bivariate.totalDegree (triSpecializeX R x) :=
      positiveChild_totalDegree_le (triSpecializeX R x) J hB hJ
    _ = Polynomial.Bivariate.totalDegree
        (Polynomial.Bivariate.evalX (Polynomial.C x) R) := by
      congr 1
      simp [triSpecializeX, Polynomial.Bivariate.evalX_eq_map]
    _ ≤ D := evalX_totalDegree_le_of_yzCap x R hYZ

end ProximityPrize.SubmissionLower
