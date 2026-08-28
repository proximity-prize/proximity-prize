import ProximityPrize.SubmissionLower.BCHKSCrossChildRouting6400
import ProximityPrize.SubmissionLower.BCHKSHenselBaseZAlignment

namespace ProximityPrize.SubmissionLower

open Polynomial Polynomial.Bivariate RationalFunctions
open RationalFunctions.HenselNumerators
open RationalFunctions.HenselNumerators.ConcreteFiniteNumerators

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

/-! The fixed-owner bridge needed by the near-full score-64 route.  Unlike a
challenge-by-challenge factor choice, the owner below is selected after mapping
the whole coordinate parent into the selected function field.  It is therefore
independent of the later specialization parameter. -/

/-- A function-field root of a nonzero bivariate parent is carried by one of
its positive normalized factors over the original coefficient ring. -/
theorem exists_positiveChild_lift_eval_eq_zero
    {H : F[X][Y]} [Fact (Irreducible H)] [Fact (0 < H.natDegree)]
    (B : F[X][Y]) (hB : B ≠ 0) (y : 𝕃 H)
    (hroot : (B.map (liftToFunctionField (H := H))).eval y = 0) :
    ∃ J ∈ positiveChildren B,
      (J.map (liftToFunctionField (H := H))).eval y = 0 := by
  let phi : F[X][Y] →+* 𝕃 H :=
    (Polynomial.evalRingHom y).comp
      (Polynomial.mapRingHom (liftToFunctionField (H := H)))
  have hphi : phi B = 0 := by
    simpa [phi] using hroot
  obtain ⟨J, hJ, hJzero⟩ :=
    exists_normalizedFactor_map_eq_zero (Q := B) phi hB hphi
  have hpos : 0 < J.natDegree := by
    apply Nat.pos_of_ne_zero
    intro hdeg
    obtain ⟨c, hc⟩ := Polynomial.natDegree_eq_zero.mp hdeg
    have hcmap : liftToFunctionField (H := H) c = 0 := by
      simpa [phi, <- hc] using hJzero
    have hc0 : c = 0 := by
      by_contra hcne
      exact liftToFunctionField_ne_zero (H := H) hcne hcmap
    have hC0 : Polynomial.C c = (0 : F[X][Y]) := by
      simpa using congrArg (Polynomial.C : F[X] → F[X][Y]) hc0
    have hJ0 : J = 0 := hc.symm.trans hC0
    exact (UniqueFactorizationMonoid.prime_of_normalized_factor J hJ).ne_zero hJ0
  exact ⟨J, mem_positiveChildren_iff.mpr ⟨hJ, hpos⟩, by simpa [phi] using hJzero⟩

/-- A positive normalized factor carrying an affine polynomial identity is
associated to that affine graph. -/
theorem positiveChild_affineIdentity_associated_linear_lift
    (B J : F[X][Y]) (a b : F)
    (hJ : J ∈ positiveChildren B)
    (hidentity :
      Polynomial.eval
        (Polynomial.C a + Polynomial.X * Polynomial.C b) J = 0) :
    Associated J
      (Polynomial.X - Polynomial.C
        (Polynomial.C a + Polynomial.X * Polynomial.C b)) := by
  let L : F[X][Y] :=
    Polynomial.X - Polynomial.C
      (Polynomial.C a + Polynomial.X * Polynomial.C b)
  have hLdvd : L ∣ J := by
    rw [Polynomial.dvd_iff_isRoot]
    simpa [L] using hidentity
  have hJirr : Irreducible J :=
    (UniqueFactorizationMonoid.prime_of_normalized_factor J
      (mem_positiveChildren_iff.mp hJ).1).irreducible
  have hLirr : Irreducible L := by
    change Irreducible
      (Polynomial.X - Polynomial.C
        (Polynomial.C a + Polynomial.X * Polynomial.C b))
    exact Polynomial.irreducible_X_sub_C _
  exact (hJirr.dvd_iff.mp hLdvd).resolve_left hLirr.not_isUnit

/-- The function-field root of a globally owned affine graph factor is the
corresponding affine function of the base coordinate. -/
theorem lift_root_eq_affine_of_affineIdentityOwner
    {H : F[X][Y]} [Fact (Irreducible H)] [Fact (0 < H.natDegree)]
    (B J : F[X][Y]) (a b : F) (y : 𝕃 H)
    (hJ : J ∈ positiveChildren B)
    (hidentity :
      Polynomial.eval
        (Polynomial.C a + Polynomial.X * Polynomial.C b) J = 0)
    (hroot : (J.map (liftToFunctionField (H := H))).eval y = 0) :
    y = fieldTo𝕃 (H := H) a +
      liftToFunctionField (H := H) Polynomial.X * fieldTo𝕃 (H := H) b := by
  let L : F[X][Y] :=
    Polynomial.X - Polynomial.C
      (Polynomial.C a + Polynomial.X * Polynomial.C b)
  have hassoc : Associated J L := by
    simpa [L] using
      positiveChild_affineIdentity_associated_linear_lift B J a b hJ hidentity
  obtain ⟨C, hLC⟩ := hassoc.dvd
  have hrootL :
      (L.map (liftToFunctionField (H := H))).eval y = 0 := by
    rw [hLC, Polynomial.map_mul, Polynomial.eval_mul, hroot, zero_mul]
  have hplain :
      y = liftToFunctionField (H := H)
        (Polynomial.C a + Polynomial.X * Polynomial.C b) := by
    simpa only [L, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C,
      Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C,
      sub_eq_zero] using hrootL
  rw [map_add, map_mul] at hplain
  change y = liftToFunctionField (H := H) (Polynomial.C a) +
    liftToFunctionField (H := H) Polynomial.X *
      liftToFunctionField (H := H) (Polynomial.C b)
  exact hplain

/-- The concrete numerator/denominator presentation is a `GoodAt` witness for
the corresponding finite-Hensel coefficient. -/
theorem finiteAlpha_goodAt_concreteSpecializedAlpha
    {H : F[X][Y]} [Fact (Irreducible H)] [Fact (0 < H.natDegree)]
    (x₀ : F) (R : F[X][X][Y])
    (hHyp : HenselNumerators.Hypotheses x₀ R H)
    (hzeta : HenselNumerators.zeta R x₀ H ≠ 0)
    (N n : ℕ) (hn : n ≤ N) (z : F)
    (root : rationalRoot (monicize H) z)
    (hden : piZ z root (concreteDenRegularBridge x₀ R hHyp n) ≠ 0) :
    GoodAt z root (finiteAlpha (R := R) (H := H) x₀ N n)
      (concreteSpecializedAlpha x₀ R hHyp hzeta N z root n) := by
  refine ⟨concreteBetaUpTo x₀ R hHyp hzeta N n,
    concreteDenRegularBridge x₀ R hHyp n, ?_, hden, rfl⟩
  rw [concreteBetaUpTo_eq_betaRegular x₀ R hHyp hzeta N n hn]
  exact embedding_betaRegular_eq_finiteAlpha_mul_denRegularBridge
    x₀ R hHyp hzeta N n hn

/-- At a selected non-pole challenge, the canonical shifted Hensel polynomial
specializes coefficientwise to the selected exact polynomial. -/
theorem canonicalFunctionFieldGamma_polyGoodAt
    {H : F[X][Y]} [Fact (Irreducible H)] [Fact (0 < H.natDegree)]
    (x₀ : F) (R : F[X][X][Y])
    (hHyp : HenselNumerators.Hypotheses x₀ R H)
    (hzeta : HenselNumerators.zeta R x₀ H ≠ 0)
    (N k : ℕ) (hkN : k ≤ N) (z : F)
    (root : rationalRoot (monicize H) z) (P : F[X])
    (hPdeg : P.natDegree ≤ k)
    (hspecializes : ∀ i, i ≤ k →
      concreteSpecializedAlpha x₀ R hHyp hzeta N z root i =
        FiniteHensel.TaylorCoeff P x₀ i)
    (hden : ∀ i, i ≤ k →
      piZ z root (concreteDenRegularBridge x₀ R hHyp i) ≠ 0) :
    PolyGoodAt z root (canonicalFunctionFieldGamma H x₀ R N k) P := by
  have hcoeff : ∀ i, i ≤ k →
      GoodAt z root (finiteAlpha (R := R) (H := H) x₀ N i)
        (FiniteHensel.TaylorCoeff P x₀ i) := by
    intro i hi
    rw [← hspecializes i hi]
    exact finiteAlpha_goodAt_concreteSpecializedAlpha
      x₀ R hHyp hzeta N i (hi.trans hkN) z root (hden i hi)
  have htrunc := PolyGoodAt.truncSeries
    (z := z) (root := root)
    (fun i => finiteAlpha (R := R) (H := H) x₀ N i)
    (fun i => FiniteHensel.TaylorCoeff P x₀ i) k hcoeff
  have hinner : PolyGoodAt z root
      (Polynomial.X - Polynomial.C (fieldTo𝕃 (H := H) x₀))
      (Polynomial.X - Polynomial.C x₀) := by
    simpa [sub_eq_add_neg] using
      PolyGoodAt.add (PolyGoodAt.X (H := H) z root)
        (PolyGoodAt.C (GoodAt.neg (GoodAt.fieldTo𝕃 (H := H) z root x₀)))
  have hcomp := PolyGoodAt.comp htrunc hinner
  have hTaylor := FiniteHensel.truncSeries_TaylorCoeff_eq_shift P x₀ k hPdeg
  have hcancel :
      (P.comp (Polynomial.C x₀ + Polynomial.X)).comp
          (Polynomial.X - Polynomial.C x₀) = P := by
    rw [Polynomial.comp_assoc]
    have hi :
        (Polynomial.C x₀ + Polynomial.X).comp
            (Polynomial.X - Polynomial.C x₀) = (Polynomial.X : F[X]) := by
      simp
    rw [hi, Polynomial.comp_X]
  unfold canonicalFunctionFieldGamma
  rw [hTaylor] at hcomp
  rw [hcancel] at hcomp
  exact hcomp

/-- Mapping a base polynomial into the function field and then evaluating at
a good value specializes to the expected finite evaluation. -/
theorem mappedPolynomial_eval_goodAt
    {H : F[X][Y]} [Fact (Irreducible H)] [Fact (0 < H.natDegree)]
    (J : F[X][Y]) (z : F) (root : rationalRoot (monicize H) z)
    (y : 𝕃 H) (v : F) (hy : GoodAt z root y v) :
    GoodAt z root
      ((J.map (liftToFunctionField (H := H))).eval y)
      ((J.map (Polynomial.evalRingHom z)).eval v) := by
  apply PolyGoodAt.eval₂_of_induction z root
    (J.map (liftToFunctionField (H := H)))
    (J.map (Polynomial.evalRingHom z)) y v _ hy
  intro i
  simp only [Polynomial.coeff_map]
  exact GoodAt.liftToFunctionField (H := H) z root (J.coeff i)

/-- A fixed generic owner remains an owner after every good specialization. -/
theorem fixedOwner_specializes_root
    {H : F[X][Y]} [Fact (Irreducible H)] [Fact (0 < H.natDegree)]
    (J : F[X][Y]) (z : F) (root : rationalRoot (monicize H) z)
    (y : 𝕃 H) (v : F) (hy : GoodAt z root y v)
    (hroot : (J.map (liftToFunctionField (H := H))).eval y = 0) :
    (J.map (Polynomial.evalRingHom z)).eval v = 0 := by
  have hgood := mappedPolynomial_eval_goodAt J z root y v hy
  rw [hroot] at hgood
  exact GoodAt.value_unique hgood (GoodAt.zero (H := H) z root)

/-- The fixed obstruction obtained by inserting the received affine line into
one fixed generic owner. -/
noncomputable def fixedAffineOwnerObstruction
    (J : F[X][Y]) (a b : F) : F[X] :=
  Polynomial.eval
    (Polynomial.C a + Polynomial.X * Polynomial.C b) J

theorem fixedAffineOwnerObstruction_eval
    (J : F[X][Y]) (a b z : F) :
    (fixedAffineOwnerObstruction J a b).eval z =
      (J.map (Polynomial.evalRingHom z)).eval (a + z * b) := by
  induction J using Polynomial.induction_on' with
  | add J K hJ hK =>
      simpa [fixedAffineOwnerObstruction] using
        congrArg₂ (fun x y : F => x + y) hJ hK
  | monomial n c =>
      simp [fixedAffineOwnerObstruction, Polynomial.map_monomial,
        Polynomial.eval_monomial, mul_comm b z]

/-- Fixed-owner dichotomy.  Either the owner is globally the affine graph, or
every agreeing good challenge is a root of one fixed univariate obstruction.
This avoids pairwise resultants and their extra Y-degree factor. -/
theorem generic_affine_or_fixedObstruction_root
    {H : F[X][Y]} [Fact (Irreducible H)] [Fact (0 < H.natDegree)]
    (B J : F[X][Y]) (hJ : J ∈ positiveChildren B)
    (a b z : F) (root : rationalRoot (monicize H) z)
    (y : 𝕃 H) (v : F)
    (hy : GoodAt z root y v)
    (hgeneric : (J.map (liftToFunctionField (H := H))).eval y = 0)
    (hagree : v = a + z * b) :
    y = fieldTo𝕃 (H := H) a +
        liftToFunctionField (H := H) Polynomial.X * fieldTo𝕃 (H := H) b ∨
      (fixedAffineOwnerObstruction J a b).eval z = 0 := by
  by_cases hzero : fixedAffineOwnerObstruction J a b = 0
  · left
    exact lift_root_eq_affine_of_affineIdentityOwner
      B J a b y hJ hzero hgeneric
  · right
    rw [fixedAffineOwnerObstruction_eval, ← hagree]
    exact fixedOwner_specializes_root J z root y v hy hgeneric

end ProximityPrize.SubmissionLower
