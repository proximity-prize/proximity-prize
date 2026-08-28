import ProximityPrize.SubmissionLower.BCHKSUniversalRootedNumerators
import ProximityPrize.SubmissionLower.BCHKSUniversalConcreteShiftCaps
import ProximityPrize.SubmissionLower.BCHKSUniversalAffineObstruction
import ProximityPrize.SubmissionLower.BCHKSUniversalResultantSelection

namespace ProximityPrize.SubmissionLower

open Polynomial Polynomial.Bivariate
open RationalFunctions RationalFunctions.HenselNumerators
open RationalFunctions.HenselNumerators.ConcreteFiniteNumerators

namespace UniversalNumerator

noncomputable section

variable {F : Type} [Field F]

/-- Universal evaluation of the symbolic `(Z,Y)` coefficient ring into an
arbitrary target field. -/
def evalUniversal {L : Type} [Field L] (φ : F[X] →+* L) (y : L) :
    F[X][Y] →+* L := Polynomial.eval₂RingHom φ y

theorem map_shiftXToUniversal_evalUniversal
    {L : Type} [Field L] (φ : F[X] →+* L) (x₀ : F) (y : L)
    (A : F[X][X]) :
    (shiftXToUniversal x₀ A).map (evalUniversal φ y) =
      FiniteHensel.shiftMap (φ (Polynomial.C x₀)) (A.map φ) := by
  induction A using Polynomial.induction_on' with
  | add A B hA hB => simp [hA, hB]
  | monomial n c =>
      simp [shiftXToUniversal, zToUniversalU, evalUniversal,
        FiniteHensel.shiftMap, Polynomial.map_monomial,
        Polynomial.eval_monomial]

theorem universalShift_map_evalUniversal
    {L : Type} [Field L] (φ : F[X] →+* L) (x₀ : F) (y : L)
    (R : F[X][X][Y]) :
    (universalShift x₀ R).map
        (Polynomial.mapRingHom (evalUniversal φ y)) =
      ((R.map (Polynomial.mapRingHom φ)).map
        (FiniteHensel.shiftMap (φ (Polynomial.C x₀)))).comp
          (Polynomial.C (Polynomial.C y) + Polynomial.X : L[X][Y]) := by
  induction R using Polynomial.induction_on' with
  | add A B hA hB =>
      rw [show universalShift x₀ (A + B) =
          universalShift x₀ A + universalShift x₀ B by
        simp [universalShift]]
      rw [Polynomial.map_add, hA, hB]
      simp
  | monomial n A =>
      have hcoeff := map_shiftXToUniversal_evalUniversal φ x₀ y A
      have hyvar : evalUniversal φ y (Polynomial.X : F[X][Y]) = y := by
        simp [evalUniversal]
      simp [universalShift, Polynomial.map_monomial, hcoeff, hyvar]

theorem universalSlope_evalUniversal
    {L : Type} [Field L] (φ : F[X] →+* L) (x₀ : F) (y : L)
    (R : F[X][X][Y]) :
    evalUniversal φ y (universalSlope x₀ R) =
      FiniteHensel.ySlope (R.map (Polynomial.mapRingHom φ))
        (φ (Polynomial.C x₀)) y := by
  unfold universalSlope evalUniversal triSpecializeX FiniteHensel.ySlope
  rw [Polynomial.derivative_map]
  change Polynomial.eval₂ φ y
      (Polynomial.map (Polynomial.evalRingHom (Polynomial.C x₀)) R.derivative) =
    Polynomial.eval₂ (Polynomial.evalRingHom (φ (Polynomial.C x₀))) y
      (Polynomial.map (Polynomial.mapRingHom φ) R.derivative)
  induction R.derivative using Polynomial.induction_on' with
  | add A B hA hB => simp [hA, hB]
  | monomial n A =>
      simp [Polynomial.map_monomial, Polynomial.eval_monomial,
        eval_map_eval_eq_eval_eval_C]

def positiveCoeffs {L : Type} [Field L] (c : ℕ → L) : ℕ → L :=
  fun i => if i = 0 then 0 else c i

theorem truncSeries_positive_add_C {L : Type} [Field L]
    (c : ℕ → L) (y : L) (N : ℕ) (hc0 : c 0 = y) :
    FiniteHensel.truncSeries (positiveCoeffs c) N + Polynomial.C y =
      FiniteHensel.truncSeries c N := by
  unfold FiniteHensel.truncSeries
  ext i
  by_cases hi : i = 0
  · subst i; simp [positiveCoeffs, hc0]
  · by_cases hiN : i ≤ N
    · simp [positiveCoeffs, hi, hiN, Polynomial.coeff_C]
    · simp [positiveCoeffs, hi, hiN, Polynomial.coeff_C]

theorem shiftedResidual_eq {L : Type} [Field L]
    (R : L[X][Y]) (x y : L) (c : ℕ → L) (N : ℕ)
    (hc0 : c 0 = y) :
    FiniteHensel.residual
      (((R.map (FiniteHensel.shiftMap x)).comp
        (Polynomial.C (Polynomial.C y) + Polynomial.X))) 0
      (positiveCoeffs c) N = FiniteHensel.residual R x c N := by
  unfold FiniteHensel.residual
  have hshift0 : FiniteHensel.shiftMap (0 : L) = RingHom.id L[X] := by
    ext a <;> simp [FiniteHensel.shiftMap]
  rw [hshift0]
  rw [Polynomial.eval₂_eq_eval_map, Polynomial.eval₂_eq_eval_map]
  rw [Polynomial.map_id]
  rw [Polynomial.eval_comp]
  have harg : (Polynomial.C (Polynomial.C y) + Polynomial.X : L[X][Y]).eval
      (FiniteHensel.truncSeries (positiveCoeffs c) N) =
      FiniteHensel.truncSeries c N := by
    simp only [Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_X]
    rw [add_comm]
    exact truncSeries_positive_add_C c y N hc0
  rw [harg]

theorem liftedR_eval_at_initial_eq_specialization
    {H : F[X][Y]} [Fact (Irreducible H)] [Fact (0 < H.natDegree)]
    (x₀ : F) (R : F[X][X][Y]) :
    Polynomial.eval₂ (Polynomial.evalRingHom (fieldTo𝕃 (H := H) x₀))
        (initialValue (H := H)) (liftedR (R := R) (H := H)) =
      Polynomial.eval₂ (liftToFunctionField (H := H))
        (initialValue (H := H)) (triSpecializeX R x₀) := by
  unfold liftedR triSpecializeX fieldTo𝕃
  induction R using Polynomial.induction_on' with
  | add A B hA hB =>
      simp only [Polynomial.map_add, Polynomial.eval₂_add]
      change
        Polynomial.eval₂ (Polynomial.evalRingHom
            ((liftToFunctionField (H := H)).comp Polynomial.C x₀))
            (initialValue (H := H))
            (A.map (Polynomial.mapRingHom (liftToFunctionField (H := H)))) +
          Polynomial.eval₂ (Polynomial.evalRingHom
            ((liftToFunctionField (H := H)).comp Polynomial.C x₀))
            (initialValue (H := H))
            (B.map (Polynomial.mapRingHom (liftToFunctionField (H := H)))) = _
      rw [hA, hB]
  | monomial n A =>
      simp [Polynomial.map_monomial, Polynomial.eval_monomial,
        eval_map_eval_eq_eval_eval_C]

/-- The complete branch-independent numerator sequence attached to an outer
factor.  Index zero is the symbolic root `Y`; positive indices are the
universal implicit numerators. -/
def universalRootedNumerators (x₀ : F) (R : F[X][X][Y]) : ℕ → F[X][Y] :=
  rootedNumerators (A := F[X][Y]) (Polynomial.X : F[X][Y])
    (universalShift x₀ R)
    (universalSlope x₀ R) R.natDegree

/-- The universal affine obstruction used for one RS coordinate. -/
def concreteUniversalAffineObstruction
    (x₀ : F) (R : F[X][X][Y]) (E k : ℕ) (dx u₀ u₁ : F) : F[X][Y] :=
  universalAffineObstruction (F := F) (universalRootedNumerators x₀ R)
    (universalSlope x₀ R : F[X][Y]) E k dx u₀ u₁

/-- After specializing `(Z,Y)=(z,y)`, the doubly shifted universal outer
factor has the shifted exact root `P(x₀+U)-y`. -/
theorem specialized_universalShift_exact
    (x₀ z y : F) (R : F[X][X][Y]) (P : F[X])
    (hExact : (triSpecializeZ R z).eval P = 0) :
    (((triSpecializeZ R z).map
        (FiniteHensel.shiftMap x₀)).comp
          (Polynomial.C (Polynomial.C y) + Polynomial.X)).eval
      (P.comp (Polynomial.C x₀ + Polynomial.X) - Polynomial.C y) = 0 := by
  rw [Polynomial.eval_comp]
  have harg : (Polynomial.C (Polynomial.C y) + Polynomial.X).eval
      (P.comp (Polynomial.C x₀ + Polynomial.X) - Polynomial.C y) =
      P.comp (Polynomial.C x₀ + Polynomial.X) := by
    simp
  rw [harg, ← FiniteHensel.shiftMap_apply]
  rw [Polynomial.eval_map]
  simp [hExact]

/-- Concrete finite-seed representation of every rooted universal numerator
as a Taylor coefficient with the exact odd denominator exponent. -/
theorem biEval_universalRootedNumerators
    (x₀ z y : F) (R : F[X][X][Y]) (P : F[X])
    (hRdeg : 0 < R.natDegree)
    (hy : P.eval x₀ = y)
    (hExact : (triSpecializeZ R z).eval P = 0)
    (hsimple : FiniteHensel.ySlope (triSpecializeZ R z) x₀ y ≠ 0) :
    ∀ n, biEval (universalRootedNumerators x₀ R n) y z =
      FiniteHensel.TaylorCoeff P x₀ n *
        biEval (universalSlope x₀ R : F[X][Y]) y z ^
          FiniteHenselWeight.denominatorExponent n := by
  intro n
  let V := P.comp (Polynomial.C x₀ + Polynomial.X) - Polynomial.C y
  let Rₛ := ((triSpecializeZ R z).map (FiniteHensel.shiftMap x₀)).comp
    (Polynomial.C (Polynomial.C y) + Polynomial.X)
  have hmap : evalZY z y (universalRootedNumerators x₀ R n) =
      rootedNumerators y Rₛ
        (FiniteHensel.ySlope (triSpecializeZ R z) x₀ y) R.natDegree n := by
    unfold universalRootedNumerators
    rw [rootedNumerators_map]
    rw [universalShift_map_evalZY, universalSlope_eval]
    have hrootEval : evalZY z y (Polynomial.X : F[X][Y]) = y := by
      simp [evalZY]
    rw [hrootEval]
  have hV0 : V.coeff 0 = 0 := by
    rw [show V.coeff 0 =
      (P.comp (Polynomial.C x₀ + Polynomial.X)).coeff 0 - y by
        simp [V]]
    rw [Polynomial.coeff_zero_eq_eval_zero, Polynomial.eval_comp]
    apply sub_eq_zero.mpr
    simpa using hy
  have hRₛdeg : Rₛ.natDegree ≤ R.natDegree := by
    dsimp [Rₛ]
    rw [Polynomial.natDegree_comp]
    have hinner :
        (Polynomial.C (Polynomial.C y) + Polynomial.X : F[X][X]).natDegree = 1 := by
      simp [add_comm]
    rw [hinner, mul_one]
    exact Polynomial.natDegree_map_le.trans Polynomial.natDegree_map_le
  have hslope : FiniteHensel.ySlope Rₛ 0 0 =
      FiniteHensel.ySlope (triSpecializeZ R z) x₀ y := by
    simp [Rₛ, FiniteHensel.ySlope, FiniteHensel.shiftMap,
      Polynomial.derivative_comp, Polynomial.eval_comp,
      Polynomial.eval₂_at_apply, eval_map_eval_eq_eval_eval_C]
    rw [Polynomial.coeff_zero_eq_eval_zero, Polynomial.eval_comp]
    simp only [Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_X,
      add_zero]
    rw [Polynomial.eval_map]
    change (Polynomial.evalRingHom 0)
      (Polynomial.eval₂ (FiniteHensel.shiftMap x₀) (Polynomial.C y)
        (triSpecializeZ R z).derivative) = _
    rw [Polynomial.hom_eval₂]
    have hcomp : (Polynomial.evalRingHom 0).comp (FiniteHensel.shiftMap x₀) =
        Polynomial.evalRingHom x₀ := by
      ext a <;> simp [FiniteHensel.shiftMap, RingHom.comp_apply]
    rw [hcomp]
    simp
  have hrepr := rootedNumerators_eq_slope_pow_mul_root_coeff
    y Rₛ V (FiniteHensel.ySlope (triSpecializeZ R z) x₀ y)
      hsimple R.natDegree hV0 hRₛdeg hslope
      (specialized_universalShift_exact x₀ z y R P hExact) n
  rw [← evalZY_apply, hmap, hrepr]
  have hsEval : biEval (universalSlope x₀ R : F[X][Y]) y z =
      FiniteHensel.ySlope (triSpecializeZ R z) x₀ y := by
    rw [← evalZY_apply, universalSlope_eval]
  rw [hsEval]
  by_cases hn : n = 0
  · subst n
    simp [FiniteHensel.TaylorCoeff, Polynomial.coeff_zero_eq_eval_zero,
      Polynomial.eval_comp, hy]
  · have hVcoeff : V.coeff n = FiniteHensel.TaylorCoeff P x₀ n := by
      rw [show V.coeff n =
        (P.comp (Polynomial.C x₀ + Polynomial.X)).coeff n -
          (Polynomial.C y).coeff n by simp [V]]
      rw [Polynomial.coeff_C, if_neg hn]
      simp [FiniteHensel.TaylorCoeff]
    rw [if_neg hn, hVcoeff]
    ring

/-- Exact finite common-root identity for the coordinate obstruction. -/
theorem biEval_concreteUniversalAffineObstruction_eq_zero
    (x₀ z y : F) (R : F[X][X][Y]) (P : F[X])
    (E k : ℕ) (dx u₀ u₁ : F)
    (hE : E = FiniteHenselWeight.denominatorExponent k)
    (hRdeg : 0 < R.natDegree)
    (hy : P.eval x₀ = y)
    (hPdeg : P.natDegree ≤ k)
    (hExact : (triSpecializeZ R z).eval P = 0)
    (hsimple : FiniteHensel.ySlope (triSpecializeZ R z) x₀ y ≠ 0)
    (haffine : P.eval (x₀ + dx) = u₀ + z * u₁) :
    biEval (concreteUniversalAffineObstruction x₀ R E k dx u₀ u₁) y z = 0 := by
  unfold concreteUniversalAffineObstruction
  apply biEval_universalAffineObstruction_eq_zero
    (c := FiniteHensel.TaylorCoeff P x₀)
  · intro i hi
    rw [hE]
    exact denominatorExponent_mono hi
  · intro i hi
    exact biEval_universalRootedNumerators x₀ z y R P hRdeg hy hExact hsimple i
  · rw [← haffine]
    calc
      (∑ i ∈ Finset.range (k + 1),
          FiniteHensel.TaylorCoeff P x₀ i * dx ^ i) =
          (FiniteHensel.truncSeries (FiniteHensel.TaylorCoeff P x₀) k).eval dx := by
            change _ = (Polynomial.evalRingHom dx)
              (∑ i ∈ Finset.range (k + 1),
                Polynomial.C (FiniteHensel.TaylorCoeff P x₀ i) *
                  Polynomial.X ^ i)
            rw [map_sum]
            simp
      _ = (P.comp (Polynomial.C x₀ + Polynomial.X)).eval dx := by
        rw [FiniteHensel.truncSeries_TaylorCoeff_eq_shift P x₀ k hPdeg]
      _ = P.eval (x₀ + dx) := by simp [Polynomial.eval_comp]

/-- Concrete bidegree endpoint consumed by the aggregate all-pair resultant
ledger. -/
theorem concreteUniversalAffineObstruction_degree_bounds
    (x₀ : F) (R : F[X][X][Y]) (E k d D : ℕ) (dx u₀ u₁ : F)
    (hE : E = FiniteHenselWeight.denominatorExponent k)
    (hk : 0 < k) (hd : 0 < d) (hD : 0 < D) (hRpos : 0 < R.natDegree)
    (hRdeg : R.natDegree ≤ d) (hYZ :
      RationalFunctions.HenselNumerators.ConcreteFiniteNumerators.YZCap R D) :
    (concreteUniversalAffineObstruction x₀ R E k dx u₀ u₁).natDegree ≤ E * d ∧
      Bivariate.degreeX
        (concreteUniversalAffineObstruction x₀ R E k dx u₀ u₁) ≤ E * D := by
  have hc := universalShift_concrete_caps x₀ R R.natDegree D le_rfl hYZ
  have hsY := universalSlope_natDegree_le_sub_one x₀ R d hRdeg
  have hsYraw := universalSlope_natDegree_le_sub_one x₀ R R.natDegree le_rfl
  have hsZ := universalSlope_degreeX_le_sub_one x₀ R D hD hYZ
  unfold concreteUniversalAffineObstruction
  apply universalAffineObstruction_degree_bounds
    (hE := hE) (hk := hk) (hd := hd) (hD := hD)
    (hsY := hsY) (hsZ := hsZ)
  · simp [universalRootedNumerators, rootedNumerators]
  · simp [universalRootedNumerators, rootedNumerators, Bivariate.degreeX]
  · intro i hi hik
    unfold universalRootedNumerators
    rw [rootedNumerators_of_pos _ _ _ _ _ hi]
    have hn := numerators_natDegree_le
      (universalShift x₀ R) (universalSlope x₀ R)
        R.natDegree hRpos hc.1 hsYraw i hi
    exact hn.trans (Nat.mul_le_mul_left
      (FiniteHenselWeight.denominatorExponent i) hRdeg)
  · intro i hi hik
    unfold universalRootedNumerators
    rw [rootedNumerators_of_pos _ _ _ _ _ hi]
    simpa [FiniteHenselWeight.denominatorExponent] using
      numerators_degreeX_le (universalShift x₀ R) (universalSlope x₀ R)
        R.natDegree D hc.2 (hsZ.trans (Nat.sub_le D 1)) i hi

end

end UniversalNumerator

end ProximityPrize.SubmissionLower
