import ProximityPrize.SubmissionLower.BCHKSUniversalNumeratorFunctionField
import ProximityPrize.SubmissionLower.BCHKSUniversalSelectedPairCore
import ProximityPrize.SubmissionLower.BCHKSFixedTransportOwner6400
import ProximityPrize.SubmissionLower.BCHKSCoordinateOwners6400

/-!
# Universal selected-pair core without primitive-cofactor hypotheses

The universal rooted numerators clear only powers of the actual generic
slope.  Consequently a divisor branch with nonzero slope is sufficient for
specialization and alignment; the stronger primitive/full-degree cofactor
package used by the regular-numerator route is unnecessary here.
-/

namespace ProximityPrize.SubmissionLower

open Polynomial Polynomial.Bivariate RationalFunctions
open RationalFunctions.HenselNumerators
open RationalFunctions.HenselNumerators.ConcreteFiniteNumerators
open UniversalNumerator

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

set_option maxRecDepth 1000000
set_option maxHeartbeats 8000000

/-- The bivariate total degree is bounded by the sum of the two separate
degrees. -/
theorem bivariate_totalDegree_le_natDegree_add_degreeX
    (B : F[X][Y]) :
    Polynomial.Bivariate.totalDegree B ≤
      B.natDegree + Polynomial.Bivariate.degreeX B := by
  classical
  unfold Polynomial.Bivariate.totalDegree
  apply Finset.sup_le
  intro j hj
  have hjdeg : j ≤ B.natDegree := Polynomial.le_natDegree_of_mem_supp j hj
  have hcoeff := Polynomial.Bivariate.coeff_natDegree_le_degreeX B j
  omega

/-- More roots on one affine graph than the total degree force that graph's
linear polynomial to divide the bivariate relation. -/
theorem affine_graph_dvd_of_many_biEval_roots
    (B : F[X][Y]) (a b : F) (S : Finset F)
    (hroot : ∀ z ∈ S, biEval B (a + z * b) z = 0)
    (hlarge : Polynomial.Bivariate.totalDegree B < S.card) :
    (Polynomial.X - Polynomial.C
      (Polynomial.C a + Polynomial.X * Polynomial.C b)) ∣ B := by
  rw [Polynomial.dvd_iff_isRoot]
  change fixedAffineOwnerObstruction B a b = 0
  apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero'
    (fixedAffineOwnerObstruction B a b) S
  · intro z hz
    rw [fixedAffineOwnerObstruction_eval]
    exact hroot z hz
  · exact (natDegree_fixedAffineOwnerObstruction_le_totalDegree B a b).trans_lt
      hlarge

/-- Concrete universal obstruction form of affine-graph root counting. -/
theorem affine_graph_dvd_concreteUniversalAffineObstruction_of_many_roots
    (x₀ a b dx u₀ u₁ : F) (R : F[X][X][Y])
    (E k d D : ℕ)
    (hE : E = FiniteHenselWeight.denominatorExponent k)
    (hk : 0 < k) (hd : 0 < d) (hD : 0 < D)
    (hRpos : 0 < R.natDegree) (hRdeg : R.natDegree ≤ d)
    (hYZ : YZCap R D)
    (S : Finset F)
    (hroot : ∀ z ∈ S,
      biEval (concreteUniversalAffineObstruction x₀ R E k dx u₀ u₁)
        (a + z * b) z = 0)
    (hlarge : E * d + E * D < S.card) :
    (Polynomial.X - Polynomial.C
      (Polynomial.C a + Polynomial.X * Polynomial.C b)) ∣
        concreteUniversalAffineObstruction x₀ R E k dx u₀ u₁ := by
  apply affine_graph_dvd_of_many_biEval_roots _ a b S hroot
  have hdegrees := concreteUniversalAffineObstruction_degree_bounds
    x₀ R E k d D dx u₀ u₁ hE hk hd hD hRpos hRdeg hYZ
  exact (bivariate_totalDegree_le_natDegree_add_degreeX _).trans_lt
    ((Nat.add_le_add hdegrees.1 hdegrees.2).trans_lt hlarge)

/-- The factor-specific score-64 fibre always contains a coordinate fibre of
size more than `102390000 * D`. -/
theorem score6400_exists_base_fiber_numeric
    (t D : ℕ) (hD : 0 < D) (ht : 144802557 * D < t) :
    (262144 - 76780) * t > 262144 * (102390000 * D) := by
  norm_num at ht ⊢
  nlinarith

/-- After deleting a full `D` roots for the base-slope cleanup, the retained
fibre has ample room for `k+1` universal-obstruction fibres. -/
theorem score6400_simple_owner_incidence_numeric
    (t d D : ℕ) (hdD : d ≤ D) (hD : 0 < D)
    (ht : 102389999 * D < t) :
    (262144 - 76780 - 131071) * t >
      (262144 - 131071) * (262141 * d + 262141 * D) := by
  norm_num at ht ⊢
  nlinarith

/-- Differentiation in the outer variable preserves a coefficientwise `YZ`
cap (and in fact saves one unit, which is not needed here). -/
theorem yzCap_derivative
    (R : F[X][X][Y]) (D : ℕ) (hYZ : YZCap R D) :
    YZCap R.derivative D := by
  intro i a ha
  have hcoeff :
      ((R.derivative.coeff i).coeff a) =
        (R.coeff (i + 1)).coeff a * ((i + 1 : ℕ) : F[X]) := by
    rw [Polynomial.coeff_derivative]
    have hcast : (((i + 1 : ℕ) : F[X][X])) =
        Polynomial.C (((i + 1 : ℕ) : F[X])) := by
      simp
    have hsuccCast : (((i : ℕ) : F[X][X]) + 1) =
        ((i + 1 : ℕ) : F[X][X]) := by
      rw [← Nat.cast_one, ← Nat.cast_add]
    rw [hsuccCast, hcast, Polynomial.coeff_mul_C]
  have horig : (R.coeff (i + 1)).coeff a ≠ 0 := by
    intro hzero
    rw [hcoeff, hzero, zero_mul] at ha
    exact ha rfl
  have hcap := hYZ (i + 1) a horig
  rw [hcoeff]
  have hdeg :
      ((R.coeff (i + 1)).coeff a * ((i + 1 : ℕ) : F[X])).natDegree ≤
        ((R.coeff (i + 1)).coeff a).natDegree := by
    have hscalar : (((i + 1 : ℕ) : F[X])).natDegree = 0 := by
      rw [← Polynomial.C_eq_natCast, Polynomial.natDegree_C]
    calc
      _ ≤ ((R.coeff (i + 1)).coeff a).natDegree +
          (((i + 1 : ℕ) : F[X])).natDegree := Polynomial.natDegree_mul_le
      _ ≤ ((R.coeff (i + 1)).coeff a).natDegree := by rw [hscalar]; simp
  omega

/-- The specialized affine slope has challenge degree at most the selected
factor's own `YZ` support degree. -/
theorem affineSlope_natDegree_le_of_yzCap
    (R : F[X][X][Y]) (x₀ a b : F) (D : ℕ) (hYZ : YZCap R D) :
    ((triSpecializeX R x₀).derivative.eval
      (Polynomial.C a + Polynomial.X * Polynomial.C b)).natDegree ≤ D := by
  have hcomm : (triSpecializeX R x₀).derivative =
      triSpecializeX R.derivative x₀ := by
    simp [triSpecializeX, Polynomial.derivative_map]
  rw [hcomm]
  exact (natDegree_fixedAffineOwnerObstruction_le_totalDegree
      (triSpecializeX R.derivative x₀) a b).trans (by
        rw [show triSpecializeX R.derivative x₀ =
          Polynomial.Bivariate.evalX (Polynomial.C x₀) R.derivative by
            simp [triSpecializeX, Polynomial.Bivariate.evalX_eq_map]]
        exact evalX_totalDegree_le_of_yzCap x₀ R.derivative
          (yzCap_derivative R D hYZ))

/-- Direct specialization of one canonical finite-Hensel coefficient via a
universal rooted numerator.  Only divisibility of the chosen branch and
nonvanishing of the generic and specialized slopes are used. -/
theorem finiteAlpha_goodAt_of_universalRootedNumerators
    {H : F[X][Y]} [Fact (Irreducible H)] [Fact (0 < H.natDegree)]
    (x₀ : F) (R : F[X][X][Y])
    (hdiv : H ∣ Polynomial.Bivariate.evalX (Polynomial.C x₀) R)
    (hzeta : HenselNumerators.zeta R x₀ H ≠ 0)
    (N n : ℕ) (hnN : n ≤ N)
    (z : F) (root : rationalRoot (monicize H) z) (P : F[X])
    (hx : GoodAt z root (fieldTo𝕃 (H := H) x₀) x₀)
    (hy : GoodAt z root (initialValue (H := H)) (P.eval x₀))
    (hRpos : 0 < R.natDegree)
    (hExact : (triSpecializeZ R z).eval P = 0)
    (hsimple : FiniteHensel.ySlope
      (triSpecializeZ R z) x₀ (P.eval x₀) ≠ 0) :
    GoodAt z root (finiteAlpha (R := R) (H := H) x₀ N n)
      (FiniteHensel.TaylorCoeff P x₀ n) := by
  let num : F[X][Y] := universalRootedNumerators x₀ R n
  let e : ℕ := FiniteHenselWeight.denominatorExponent n
  have hgeneric :=
    eval₂_universalRootedNumerators_eq_finiteAlpha_mul_zeta_pow_of_dvd
      x₀ R hdiv hzeta N n hnN
  have hnumGood := mappedPolynomial_eval_goodAt
    num z root (initialValue (H := H)) (P.eval x₀) hy
  have hfinite := biEval_universalRootedNumerators
    x₀ z (P.eval x₀) R P hRpos rfl hExact hsimple n
  have hgeneric' :
      ((num.map (liftToFunctionField (H := H))).eval
          (initialValue (H := H))) =
        finiteAlpha (R := R) (H := H) x₀ N n *
          HenselNumerators.zeta R x₀ H ^ e := by
    simpa [num, e, Polynomial.eval₂_eq_eval_map] using hgeneric
  have hfinite' :
      ((num.map (Polynomial.evalRingHom z)).eval (P.eval x₀)) =
        FiniteHensel.TaylorCoeff P x₀ n *
          FiniteHensel.ySlope
            (triSpecializeZ R z) x₀ (P.eval x₀) ^ e := by
    have hslopeEval :
        ((universalSlope x₀ R).map (Polynomial.evalRingHom z)).eval
            (P.eval x₀) =
          FiniteHensel.ySlope
            (triSpecializeZ R z) x₀ (P.eval x₀) := by
      simpa [evalZY] using universalSlope_eval x₀ z (P.eval x₀) R
    simpa [num, e, biEval, hslopeEval] using hfinite
  have hnumGood' : GoodAt z root
      (finiteAlpha (R := R) (H := H) x₀ N n *
        HenselNumerators.zeta R x₀ H ^ e)
      (FiniteHensel.TaylorCoeff P x₀ n *
        FiniteHensel.ySlope (triSpecializeZ R z) x₀ (P.eval x₀) ^ e) := by
    rw [hgeneric', hfinite'] at hnumGood
    exact hnumGood
  have hslope := selectedSlopeGoodAt x₀ R z root x₀ (P.eval x₀) hx hy
  have hslope' : GoodAt z root
      (HenselNumerators.zeta R x₀ H)
      (FiniteHensel.ySlope (triSpecializeZ R z) x₀ (P.eval x₀)) := by
    simpa [ySlope_liftedR_eq_zeta] using hslope
  have hquot := GoodAt.div hnumGood' (GoodAt.pow hslope' e)
    (pow_ne_zero e hsimple)
  simpa [hzeta, hsimple] using hquot

/-- Coefficientwise universal specialization assembles to specialization of
the whole canonical centered truncation. -/
theorem canonicalFunctionFieldGamma_polyGoodAt_light
    {H : F[X][Y]} [Fact (Irreducible H)] [Fact (0 < H.natDegree)]
    (x₀ : F) (R : F[X][X][Y])
    (hdiv : H ∣ Polynomial.Bivariate.evalX (Polynomial.C x₀) R)
    (hzeta : HenselNumerators.zeta R x₀ H ≠ 0)
    (N k : ℕ) (hkN : k ≤ N) (z : F)
    (root : rationalRoot (monicize H) z) (P : F[X])
    (hPdeg : P.natDegree ≤ k)
    (hx : GoodAt z root (fieldTo𝕃 (H := H) x₀) x₀)
    (hy : GoodAt z root (initialValue (H := H)) (P.eval x₀))
    (hRpos : 0 < R.natDegree)
    (hExact : (triSpecializeZ R z).eval P = 0)
    (hsimple : FiniteHensel.ySlope
      (triSpecializeZ R z) x₀ (P.eval x₀) ≠ 0) :
    PolyGoodAt z root (canonicalFunctionFieldGamma H x₀ R N k) P := by
  have hcoeff : ∀ i, i ≤ k →
      GoodAt z root (finiteAlpha (R := R) (H := H) x₀ N i)
        (FiniteHensel.TaylorCoeff P x₀ i) := by
    intro i hi
    exact finiteAlpha_goodAt_of_universalRootedNumerators
      x₀ R hdiv hzeta N i (hi.trans hkN) z root P hx hy
        hRpos hExact hsimple
  have htrunc := PolyGoodAt.truncSeries
    (z := z) (root := root)
    (fun i => finiteAlpha (R := R) (H := H) x₀ N i)
    (fun i => FiniteHensel.TaylorCoeff P x₀ i) k hcoeff
  have hinner : PolyGoodAt z root
      (Polynomial.X - Polynomial.C (fieldTo𝕃 (H := H) x₀))
      (Polynomial.X - Polynomial.C x₀) := by
    simpa [sub_eq_add_neg] using
      PolyGoodAt.add (PolyGoodAt.X (H := H) z root)
        (PolyGoodAt.C
          (GoodAt.neg (GoodAt.fieldTo𝕃 (H := H) z root x₀)))
  have hcomp := PolyGoodAt.comp htrunc hinner
  have hTaylor :=
    FiniteHensel.truncSeries_TaylorCoeff_eq_shift P x₀ k hPdeg
  have hcancel :
      (P.comp (Polynomial.C x₀ + Polynomial.X)).comp
          (Polynomial.X - Polynomial.C x₀) = P := by
    rw [Polynomial.comp_assoc]
    have hi :
        (Polynomial.C x₀ + Polynomial.X).comp
            (Polynomial.X - Polynomial.C x₀) =
          (Polynomial.X : F[X]) := by
      simp
    rw [hi, Polynomial.comp_X]
  unfold canonicalFunctionFieldGamma
  rw [hTaylor] at hcomp
  rw [hcancel] at hcomp
  exact hcomp

/-- Complete universal alignment consumer under the minimal divisor-branch
hypotheses.  This is the branch-consistency endpoint needed by the score-64
linear-owner route. -/
theorem bare_universal_selected_pair_alignment_core
    {H : F[X][Y]} [Fact (Irreducible H)] [Fact (0 < H.natDegree)]
    (x₀ : F) (R : F[X][X][Y])
    (hdiv : H ∣ Polynomial.Bivariate.evalX (Polynomial.C x₀) R)
    (hzeta : HenselNumerators.zeta R x₀ H ≠ 0)
    (hRpos : 0 < R.natDegree)
    (N k : ℕ) (hkN : k ≤ N)
    (T : Finset F) (root : ∀ z : T, rationalRoot (monicize H) (z : F))
    (P : T → F[X])
    (hx : ∀ z : T, GoodAt (z : F) (root z)
      (fieldTo𝕃 (H := H) x₀) x₀)
    (hy : ∀ z : T, GoodAt (z : F) (root z)
      (initialValue (H := H)) ((P z).eval x₀))
    (hPdeg : ∀ z, (P z).natDegree ≤ k)
    (hExact : ∀ z : T, (triSpecializeZ R (z : F)).eval (P z) = 0)
    (hsimple : ∀ z : T, FiniteHensel.ySlope
      (triSpecializeZ R (z : F)) x₀ ((P z).eval x₀) ≠ 0)
    (hkF : k < Fintype.card F)
    (A : Finset F) (hAcard : k + 1 ≤ A.card) (U₀ U₁ : F → F)
    (hzero : ∀ x ∈ A,
      Polynomial.eval₂ (liftToFunctionField (H := H))
        (initialValue (H := H))
          (concreteUniversalAffineObstruction x₀ R
            (FiniteHenselWeight.denominatorExponent k) k
            (x - x₀) (U₀ x) (U₁ x)) = 0) :
    ∃ p₀ p₁ : F[X], p₀.natDegree ≤ k ∧ p₁.natDegree ≤ k ∧
      ∀ z : T, P z = p₀ + Polynomial.C (z : F) * p₁ := by
  let γ := canonicalFunctionFieldGamma H x₀ R N k
  have hs : Polynomial.eval₂ (liftToFunctionField (H := H))
      (initialValue (H := H)) (universalSlope x₀ R) =
        HenselNumerators.zeta R x₀ H := by
    change evalUniversal (liftToFunctionField (H := H))
      (initialValue (H := H)) (universalSlope x₀ R) = _
    rw [universalSlope_evalUniversal]
    simpa [liftedR, fieldTo𝕃] using
      (ySlope_liftedR_eq_zeta (R := R) (H := H) x₀)
  have hnum : ∀ i, i ≤ k →
      Polynomial.eval₂ (liftToFunctionField (H := H))
          (initialValue (H := H)) (universalRootedNumerators x₀ R i) =
        finiteAlpha (R := R) (H := H) x₀ N i *
          HenselNumerators.zeta R x₀ H ^
            FiniteHenselWeight.denominatorExponent i := by
    intro i hi
    exact eval₂_universalRootedNumerators_eq_finiteAlpha_mul_zeta_pow_of_dvd
      x₀ R hdiv hzeta N i (hi.trans hkN)
  have hγeval : ∀ x ∈ A, γ.eval (fieldTo𝕃 (H := H) x) =
      fieldTo𝕃 (H := H) (U₀ x) +
        liftToFunctionField (H := H) Polynomial.X *
          fieldTo𝕃 (H := H) (U₁ x) := by
    intro x hxA
    apply gamma_eval_eq_affine_of_universalAffineObstruction_eq_zero_light
      x₀ x (U₀ x) (U₁ x) R hzeta N k hkN
      (universalRootedNumerators x₀ R) (universalSlope x₀ R)
      (FiniteHenselWeight.denominatorExponent k) rfl hs hnum
    simpa [concreteUniversalAffineObstruction] using hzero x hxA
  obtain ⟨p₀, p₁, hp₀, hp₁, hγ⟩ :=
    canonicalFunctionFieldGamma_baseZ_affine x₀ R N k A hAcard
      U₀ U₁ (canonicalFunctionFieldGamma_natDegree_le x₀ R N k) hγeval
  refine ⟨p₀, p₁, hp₀, hp₁, ?_⟩
  intro z
  let q := p₀ + Polynomial.C (z : F) * p₁
  apply Polynomial.eq_of_natDegree_lt_card_of_eval_eq (P z) q
    (f := fun x : F => x) Function.injective_id
  · intro x
    have hpoly := canonicalFunctionFieldGamma_polyGoodAt_light
      x₀ R hdiv hzeta N k hkN (z : F) (root z) (P z)
      (hPdeg z) (hx z) (hy z) hRpos (hExact z) (hsimple z)
    have hgood := PolyGoodAt.eval₂_of_induction
      (z : F) (root z) γ (P z) (fieldTo𝕃 (H := H) x) x
      (by simpa [γ] using hpoly)
      (GoodAt.fieldTo𝕃 (H := H) (z : F) (root z) x)
    have hall : γ.eval (fieldTo𝕃 (H := H) x) =
        fieldTo𝕃 (H := H) (p₀.eval x) +
          liftToFunctionField (H := H) Polynomial.X *
            fieldTo𝕃 (H := H) (p₁.eval x) := by
      change (canonicalFunctionFieldGamma H x₀ R N k).eval
        (fieldTo𝕃 (H := H) x) = _
      rw [hγ]
      simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_map]
      have hp0map : Polynomial.eval₂
          (liftToFunctionField (H := H) |>.comp Polynomial.C)
          (liftToFunctionField (H := H) (Polynomial.C x)) p₀ =
          liftToFunctionField (H := H) (Polynomial.C (p₀.eval x)) := by
        rw [← Polynomial.hom_eval₂ p₀ Polynomial.C
          (liftToFunctionField (H := H)) (Polynomial.C x)]
        simp
      have hp1map : Polynomial.eval₂
          (liftToFunctionField (H := H) |>.comp Polynomial.C)
          (liftToFunctionField (H := H) (Polynomial.C x)) p₁ =
          liftToFunctionField (H := H) (Polynomial.C (p₁.eval x)) := by
        rw [← Polynomial.hom_eval₂ p₁ Polynomial.C
          (liftToFunctionField (H := H)) (Polynomial.C x)]
        simp
      change Polynomial.eval₂
          (liftToFunctionField (H := H) |>.comp Polynomial.C)
          (liftToFunctionField (H := H) (Polynomial.C x)) p₀ +
        liftToFunctionField (H := H) Polynomial.X *
          Polynomial.eval₂
            (liftToFunctionField (H := H) |>.comp Polynomial.C)
            (liftToFunctionField (H := H) (Polynomial.C x)) p₁ = _
      rw [hp0map, hp1map]
      rfl
    rw [hall] at hgood
    have hZ : GoodAt (z : F) (root z)
        (liftToFunctionField (H := H) Polynomial.X) (z : F) := by
      simpa using
        (GoodAt.liftToFunctionField (H := H) (z : F) (root z) Polynomial.X)
    have hrhs : GoodAt (z : F) (root z)
        (fieldTo𝕃 (H := H) (p₀.eval x) +
          liftToFunctionField (H := H) Polynomial.X *
            fieldTo𝕃 (H := H) (p₁.eval x))
        (p₀.eval x + (z : F) * p₁.eval x) :=
      GoodAt.add
        (GoodAt.fieldTo𝕃 (H := H) (z : F) (root z) (p₀.eval x))
        (GoodAt.mul
          hZ
          (GoodAt.fieldTo𝕃 (H := H) (z : F) (root z) (p₁.eval x)))
    have heval := GoodAt.value_unique hgood hrhs
    simpa [q, Polynomial.eval_add, Polynomial.eval_mul] using heval
  · have hq : q.natDegree ≤ k := by
      exact (Polynomial.natDegree_add_le _ _).trans
        (max_le hp₀ ((Polynomial.natDegree_C_mul_le _ _).trans hp₁))
    exact max_lt ((hPdeg z).trans_lt hkF) (hq.trans_lt hkF)

/-- Instantiate the bare universal consumer with the literal affine graph
factor `Y-(a+bZ)`.  A nonempty family of simple exact sections supplies the
generic nonzero slope automatically. -/
theorem affine_graph_divisor_universal_alignment_core
    (x₀ a b : F) (R : F[X][X][Y]) (hRpos : 0 < R.natDegree)
    (hidentity : (triSpecializeX R x₀).eval
      (Polynomial.C a + Polynomial.X * Polynomial.C b) = 0)
    (N k : ℕ) (hkN : k ≤ N)
    (T : Finset F) (hTnonempty : T.Nonempty) (P : T → F[X])
    (hPdeg : ∀ z, (P z).natDegree ≤ k)
    (hExact : ∀ z : T, (triSpecializeZ R (z : F)).eval (P z) = 0)
    (hbase : ∀ z : T, (P z).eval x₀ = a + (z : F) * b)
    (hsimple : ∀ z : T, FiniteHensel.ySlope
      (triSpecializeZ R (z : F)) x₀ ((P z).eval x₀) ≠ 0)
    (hkF : k < Fintype.card F)
    (A : Finset F) (hAcard : k + 1 ≤ A.card) (U₀ U₁ : F → F)
    (hzero : ∀ x ∈ A,
      (Polynomial.X - Polynomial.C
        (Polynomial.C a + Polynomial.X * Polynomial.C b)) ∣
          concreteUniversalAffineObstruction x₀ R
            (FiniteHenselWeight.denominatorExponent k) k
            (x - x₀) (U₀ x) (U₁ x)) :
    ∃ p₀ p₁ : F[X], p₀.natDegree ≤ k ∧ p₁.natDegree ≤ k ∧
      ∀ z : T, P z = p₀ + Polynomial.C (z : F) * p₁ := by
  let L : F[X] := Polynomial.C a + Polynomial.X * Polynomial.C b
  let H : F[X][Y] := Polynomial.X - Polynomial.C L
  have hHirr : Irreducible H := by
    dsimp [H]
    exact Polynomial.irreducible_X_sub_C L
  letI : Fact (Irreducible H) := ⟨hHirr⟩
  have hHdegree : H.natDegree = 1 := by
    dsimp [H]
    simp
  letI : Fact (0 < H.natDegree) := ⟨by omega⟩
  have hdiv : H ∣ Polynomial.Bivariate.evalX (Polynomial.C x₀) R := by
    rw [Polynomial.dvd_iff_isRoot]
    have heq : Polynomial.Bivariate.evalX (Polynomial.C x₀) R =
        triSpecializeX R x₀ := by
      simp [triSpecializeX, Polynomial.Bivariate.evalX_eq_map]
    rw [heq]
    simpa [H, L] using hidentity
  have hfactor : ∀ z : T,
      Polynomial.evalEval (z : F) ((P z).eval x₀) H = 0 := by
    intro z
    dsimp [H]
    rw [Polynomial.evalEval_sub, Polynomial.evalEval_X,
      Polynomial.evalEval_C]
    dsimp [L]
    simp only [Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_X]
    rw [hbase z]
    ring
  let root : ∀ z : T, rationalRoot (monicize H) (z : F) := fun z ↦
    rationalRootOfPair H (Fact.out : 0 < H.natDegree)
      (z : F) ((P z).eval x₀) (hfactor z)
  have hx : ∀ z : T, GoodAt (z : F) (root z)
      (fieldTo𝕃 (H := H) x₀) x₀ := fun z ↦
    GoodAt.fieldTo𝕃 (H := H) (z : F) (root z) x₀
  have hW : ∀ z : T, H.leadingCoeff.eval (z : F) ≠ 0 := by
    intro z
    simp [H]
  have hy : ∀ z : T, GoodAt (z : F) (root z)
      (initialValue (H := H)) ((P z).eval x₀) := by
    intro z
    have hT : GoodAt (z : F) (root z) (functionFieldT (H := H))
        (H.leadingCoeff.eval (z : F) * (P z).eval x₀) := by
      refine ⟨Ideal.Quotient.mk (Ideal.span {monicize H}) Polynomial.X,
        1, ?_, by simp, ?_⟩
      · simpa [embedding_mk_X_eq_functionFieldT]
      · simpa [root] using
          (piZ_mk_X_rationalRootOfPair H
            (Fact.out : 0 < H.natDegree) (z : F) ((P z).eval x₀)
              (hfactor z)).symm
    have hWgood :=
      GoodAt.liftToFunctionField (H := H) (z : F) (root z) H.leadingCoeff
    simpa [initialValue, mul_div_cancel_left₀ _ (hW z)] using
      GoodAt.div hT hWgood (hW z)
  obtain ⟨z₀, hz₀⟩ := hTnonempty
  let zpick : T := ⟨z₀, hz₀⟩
  have hzeta : HenselNumerators.zeta R x₀ H ≠ 0 := by
    exact zeta_ne_zero_of_selected_slope
      x₀ R (zpick : F) (root zpick) x₀ ((P zpick).eval x₀)
        (hx zpick) (hy zpick) (hsimple zpick)
  apply bare_universal_selected_pair_alignment_core
    x₀ R hdiv hzeta hRpos N k hkN T root P hx hy hPdeg hExact hsimple
      hkF A hAcard U₀ U₁
  intro x hxA
  apply eval₂_lift_initialValue_eq_zero_of_dvd _ H
  simpa [H, L] using hzero x hxA

end ProximityPrize.SubmissionLower
