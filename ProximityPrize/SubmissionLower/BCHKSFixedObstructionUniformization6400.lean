import ProximityPrize.SubmissionLower.BCHKSCoordinateOwners6400

namespace ProximityPrize.SubmissionLower

open Polynomial Polynomial.Bivariate RationalFunctions
open RationalFunctions.HenselNumerators
open RationalFunctions.HenselNumerators.ConcreteFiniteNumerators

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

/-- Score-64 fixed-obstruction uniformization.  Once the selected canonical
gamma is an exact generic root, 4,031,860 agreeing challenges force gamma to
be globally affine in the independent base coordinate. -/
theorem fixed_obstruction_uniformizes_gamma_of_cap_6400
    {F I : Type} [Field F] [Fintype F] [DecidableEq F]
    [Fintype I] [DecidableEq I]
    {H : F[X][Y]} [Fact (Irreducible H)] [Fact (0 < H.natDegree)]
    (omega : I ↪ F) (hn : Fintype.card I = 262144)
    (x₀ : F) (R : F[X][X][Y]) (N : ℕ)
    (hN : 131071 ≤ N)
    (hRirr : Irreducible R) (hRpos : 0 < R.natDegree)
    (hHyp : HenselNumerators.Hypotheses x₀ R H)
    (hzeta : HenselNumerators.zeta R x₀ H ≠ 0)
    (D : ℕ) (hYZ : YZCap R D)
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
    (hcount :
      (262144 - 76780 - 131071) * T.card >
        (262144 - 131071) * D) :
    ∃ p₀ p₁ : F[X], p₀.natDegree ≤ 131071 ∧
      p₁.natDegree ≤ 131071 ∧
      canonicalFunctionFieldGamma H x₀ R N 131071 =
        p₀.map (groundToFunctionField H) +
          Polynomial.C (liftToFunctionField (H := H) Polynomial.X) *
            p₁.map (groundToFunctionField H) := by
  classical
  let gamma : (𝕃 H)[X] := canonicalFunctionFieldGamma H x₀ R N 131071
  let B : I → F[X][Y] := fun i => triSpecializeX R (omega i)
  have hB0 : ∀ i, B i ≠ 0 := by
    intro i
    exact triSpecializeX_ne_zero_of_irreducible_natDegree_pos
      R hRirr hRpos (omega i)
  have hcoordinateRoot : ∀ i,
      ((B i).map (liftToFunctionField (H := H))).eval
        (gamma.eval (fieldTo𝕃 (H := H) (omega i))) = 0 := by
    intro i
    exact coordinate_parent_carries_generic_root R gamma hgammaRoot (omega i)
  have howner : ∀ i, ∃ J ∈ positiveChildren (B i),
      (J.map (liftToFunctionField (H := H))).eval
        (gamma.eval (fieldTo𝕃 (H := H) (omega i))) = 0 := by
    intro i
    exact exists_positiveChild_lift_eval_eq_zero
      (B i) (hB0 i) _ (hcoordinateRoot i)
  let J : I → F[X][Y] := fun i => Classical.choose (howner i)
  have hJmem : ∀ i, J i ∈ positiveChildren (B i) := by
    intro i
    exact (Classical.choose_spec (howner i)).1
  have hJroot : ∀ i,
      ((J i).map (liftToFunctionField (H := H))).eval
        (gamma.eval (fieldTo𝕃 (H := H) (omega i))) = 0 := by
    intro i
    exact (Classical.choose_spec (howner i)).2
  let G : I → F[X] := fun i =>
    fixedAffineOwnerObstruction (J i) (U₀ i) (U₁ i)
  have hGdegree : ∀ i, (G i).natDegree ≤ D := by
    intro i
    exact fixedAffineOwnerObstruction_degree_le_of_yzCap
      R (omega i) (U₀ i) (U₁ i) (J i) D
      (hB0 i) (hJmem i) hYZ
  have hGroot : ∀ z ∈ T, ∀ i ∈ A z, (G i).eval z = 0 := by
    intro z hz i hi
    let zT : T := ⟨z, hz⟩
    have hpoly := canonicalFunctionFieldGamma_polyGoodAt
      x₀ R hHyp hzeta N 131071 hN z (root zT) (P zT)
      (hPdeg zT) (hspecializes zT) (hden zT)
    have hgood := PolyGoodAt.eval₂_of_induction z (root zT)
      gamma (P zT) (fieldTo𝕃 (H := H) (omega i)) (omega i)
      (by simpa [gamma] using hpoly)
      (GoodAt.fieldTo𝕃 (H := H) z (root zT) (omega i))
    have hgood' : GoodAt z (root zT)
        (gamma.eval (fieldTo𝕃 (H := H) (omega i)))
        (U₀ i + z * U₁ i) := by
      rw [← hagree zT i hi]
      exact hgood
    change (fixedAffineOwnerObstruction (J i) (U₀ i) (U₁ i)).eval z = 0
    rw [fixedAffineOwnerObstruction_eval]
    exact fixedOwner_specializes_root (J i) z (root zT)
      (gamma.eval (fieldTo𝕃 (H := H) (omega i)))
      (U₀ i + z * U₁ i) hgood' (hJroot i)
  have hzeroCount :
      131071 + 1 ≤ (Finset.univ.filter fun i : I => G i = 0).card := by
    apply many_zero_obstructions_of_many_large_fibers
      T A G 262144 76780 131071 D hn
    · intro z hz
      simpa using hrow z hz
    · exact hGroot
    · exact hGdegree
    · exact hcount
  let D : Finset I := Finset.univ.filter fun i : I => G i = 0
  let Dfield : Finset F := D.map omega
  have hDcard : 131071 + 1 ≤ Dfield.card := by
    simpa [Dfield, D] using hzeroCount
  haveI : Nonempty I := Fintype.card_pos_iff.mp (by rw [hn]; norm_num)
  let U₀f : F → F := fun x => U₀ (Function.invFun omega x)
  let U₁f : F → F := fun x => U₁ (Function.invFun omega x)
  have heval : ∀ x ∈ Dfield,
      gamma.eval (fieldTo𝕃 (H := H) x) =
        fieldTo𝕃 (H := H) (U₀f x) +
          liftToFunctionField (H := H) Polynomial.X *
            fieldTo𝕃 (H := H) (U₁f x) := by
    intro x hx
    obtain ⟨i, hiD, rfl⟩ := Finset.mem_map.mp hx
    have hGi : G i = 0 := (Finset.mem_filter.mp hiD).2
    have hident : fixedAffineOwnerObstruction (J i) (U₀ i) (U₁ i) = 0 := by
      simpa [G] using hGi
    have hrootAffine := lift_root_eq_affine_of_affineIdentityOwner
      (B i) (J i) (U₀ i) (U₁ i)
      (gamma.eval (fieldTo𝕃 (H := H) (omega i)))
      (hJmem i) hident (hJroot i)
    simpa [U₀f, U₁f, Function.leftInverse_invFun omega.injective i] using hrootAffine
  exact canonicalFunctionFieldGamma_baseZ_affine
    x₀ R N 131071 Dfield hDcard U₀f U₁f
    (canonicalFunctionFieldGamma_natDegree_le x₀ R N 131071)
    (by simpa [gamma] using heval)

/-- The original concrete cap is retained as a convenience wrapper. -/
theorem fixed_obstruction_uniformizes_gamma_6400
    {F I : Type} [Field F] [Fintype F] [DecidableEq F]
    [Fintype I] [DecidableEq I]
    {H : F[X][Y]} [Fact (Irreducible H)] [Fact (0 < H.natDegree)]
    (omega : I ↪ F) (hn : Fintype.card I = 262144)
    (x₀ : F) (R : F[X][X][Y]) (N : ℕ)
    (hN : 131071 ≤ N)
    (hRirr : Irreducible R) (hRpos : 0 < R.natDegree)
    (hHyp : HenselNumerators.Hypotheses x₀ R H)
    (hzeta : HenselNumerators.zeta R x₀ H ≠ 0)
    (hYZ : YZCap R 1670075)
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
    (hTcard : 4031860 ≤ T.card) :
    ∃ p₀ p₁ : F[X], p₀.natDegree ≤ 131071 ∧
      p₁.natDegree ≤ 131071 ∧
      canonicalFunctionFieldGamma H x₀ R N 131071 =
        p₀.map (groundToFunctionField H) +
          Polynomial.C (liftToFunctionField (H := H) Polynomial.X) *
            p₁.map (groundToFunctionField H) := by
  apply fixed_obstruction_uniformizes_gamma_of_cap_6400 omega hn x₀ R N hN
    hRirr hRpos hHyp hzeta 1670075 hYZ hgammaRoot T root P A U₀ U₁
    hPdeg hspecializes hden hrow hagree
  exact score6400_fixed_obstruction_large_fibers_numeric T.card hTcard

/-- Once the canonical Hensel root is affine in the independent base
coordinate, specialization at every selected challenge puts the selected
polynomial on the same affine line.  This is the denominator-safe tail of the
selected-pair argument, separated from the mechanism that uniformizes gamma. -/
theorem selected_polynomials_align_of_canonical_gamma_baseZ_affine
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {H : F[X][Y]} [Fact (Irreducible H)] [Fact (0 < H.natDegree)]
    (x₀ : F) (R : F[X][X][Y])
    (hHyp : HenselNumerators.Hypotheses x₀ R H)
    (hzeta : HenselNumerators.zeta R x₀ H ≠ 0)
    (N k : ℕ) (hkN : k ≤ N)
    (T : Finset F) (root : ∀ z : T, rationalRoot (monicize H) (z : F))
    (P : T → F[X]) (hPdeg : ∀ z, (P z).natDegree ≤ k)
    (hspecializes : ∀ z : T, ∀ i, i ≤ k →
      concreteSpecializedAlpha x₀ R hHyp hzeta N (z : F) (root z) i =
        FiniteHensel.TaylorCoeff (P z) x₀ i)
    (hden : ∀ z : T, ∀ i, i ≤ k →
      piZ (z : F) (root z) (concreteDenRegularBridge x₀ R hHyp i) ≠ 0)
    (hkF : k < Fintype.card F)
    (p₀ p₁ : F[X]) (hp₀ : p₀.natDegree ≤ k)
    (hp₁ : p₁.natDegree ≤ k)
    (hgamma : canonicalFunctionFieldGamma H x₀ R N k =
      p₀.map (groundToFunctionField H) +
        Polynomial.C (liftToFunctionField (H := H) Polynomial.X) *
          p₁.map (groundToFunctionField H)) :
    ∀ z : T, P z = p₀ + Polynomial.C (z : F) * p₁ := by
  intro z
  let q := p₀ + Polynomial.C (z : F) * p₁
  apply Polynomial.eq_of_natDegree_lt_card_of_eval_eq (P z) q
    (f := fun x : F => x) Function.injective_id
  · intro x
    have hall :
        (canonicalFunctionFieldGamma H x₀ R N k).eval
            (fieldTo𝕃 (H := H) x) =
          fieldTo𝕃 (H := H) (p₀.eval x) +
            liftToFunctionField (H := H) Polynomial.X *
              fieldTo𝕃 (H := H) (p₁.eval x) := by
      rw [hgamma]
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
    let β := explicitBaseZGammaDifferenceRegular x₀ (x - x₀)
      (p₀.eval x) (p₁.eval x) R hHyp hzeta N k hkN
    have hb0 : embeddingOf𝒪Into𝕃 H β = 0 := by
      rw [embedding_explicitBaseZGammaDifferenceRegular x₀ (x - x₀)
        (p₀.eval x) (p₁.eval x) R hHyp hzeta N k hkN]
      rw [canonicalFunctionFieldGamma_eval] at hall
      rw [hall]
      ring
    have hβzero : β = 0 := by
      apply embeddingOf𝒪Into𝕃_injective (Fact.out : 0 < H.natDegree)
      simpa using hb0
    have hpiz : piZ (z : F) (root z) β = 0 := by
      rw [hβzero]
      simp
    rw [piZ_explicitBaseZGammaDifferenceRegular_eq_zero_iff
      x₀ (x - x₀) (p₀.eval x) (p₁.eval x) (z : F) (root z)
      R hHyp hzeta N k hkN (P z) (hPdeg z)] at hpiz
    · simpa [q, sub_eq_add_neg, Polynomial.eval_add,
        Polynomial.eval_mul] using hpiz
    · exact hspecializes z
    · exact hden z
  · have hq : q.natDegree ≤ k := by
      exact (Polynomial.natDegree_add_le _ _).trans
        (max_le hp₀ ((Polynomial.natDegree_C_mul_le _ _).trans hp₁))
    exact max_lt ((hPdeg z).trans_lt hkF) (hq.trans_lt hkF)

/-- Complete fixed-obstruction selected-pair consumer.  Its inputs are exactly
the selected algebraic package still owed by the global score-64 construction;
all coordinate uniformization and specialization work is discharged here. -/
theorem fixed_obstruction_selected_pair_alignment_of_cap_6400
    {F I : Type} [Field F] [Fintype F] [DecidableEq F]
    [Fintype I] [DecidableEq I]
    {H : F[X][Y]} [Fact (Irreducible H)] [Fact (0 < H.natDegree)]
    (omega : I ↪ F) (hn : Fintype.card I = 262144)
    (x₀ : F) (R : F[X][X][Y]) (N : ℕ) (hN : 131071 ≤ N)
    (hRirr : Irreducible R) (hRpos : 0 < R.natDegree)
    (hHyp : HenselNumerators.Hypotheses x₀ R H)
    (hzeta : HenselNumerators.zeta R x₀ H ≠ 0)
    (D : ℕ) (hYZ : YZCap R D)
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
    (hcount :
      (262144 - 76780 - 131071) * T.card >
        (262144 - 131071) * D)
    (hkF : 131071 < Fintype.card F) :
    ∃ p₀ p₁ : F[X], p₀.natDegree ≤ 131071 ∧
      p₁.natDegree ≤ 131071 ∧
      ∀ z : T, P z = p₀ + Polynomial.C (z : F) * p₁ := by
  obtain ⟨p₀, p₁, hp₀, hp₁, hgamma⟩ :=
    fixed_obstruction_uniformizes_gamma_of_cap_6400 omega hn x₀ R N hN
      hRirr hRpos hHyp hzeta D hYZ hgammaRoot T root P A U₀ U₁
      hPdeg hspecializes hden hrow hagree hcount
  exact ⟨p₀, p₁, hp₀, hp₁,
    selected_polynomials_align_of_canonical_gamma_baseZ_affine
      x₀ R hHyp hzeta N 131071 hN T root P hPdeg hspecializes hden
      hkF p₀ p₁ hp₀ hp₁ hgamma⟩

theorem fixed_obstruction_selected_pair_alignment_6400
    {F I : Type} [Field F] [Fintype F] [DecidableEq F]
    [Fintype I] [DecidableEq I]
    {H : F[X][Y]} [Fact (Irreducible H)] [Fact (0 < H.natDegree)]
    (omega : I ↪ F) (hn : Fintype.card I = 262144)
    (x₀ : F) (R : F[X][X][Y]) (N : ℕ) (hN : 131071 ≤ N)
    (hRirr : Irreducible R) (hRpos : 0 < R.natDegree)
    (hHyp : HenselNumerators.Hypotheses x₀ R H)
    (hzeta : HenselNumerators.zeta R x₀ H ≠ 0)
    (hYZ : YZCap R 1670075)
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
    (hTcard : 4031860 ≤ T.card)
    (hkF : 131071 < Fintype.card F) :
    ∃ p₀ p₁ : F[X], p₀.natDegree ≤ 131071 ∧
      p₁.natDegree ≤ 131071 ∧
      ∀ z : T, P z = p₀ + Polynomial.C (z : F) * p₁ := by
  obtain ⟨p₀, p₁, hp₀, hp₁, hgamma⟩ :=
    fixed_obstruction_uniformizes_gamma_6400 omega hn x₀ R N hN
      hRirr hRpos hHyp hzeta hYZ hgammaRoot T root P A U₀ U₁
      hPdeg hspecializes hden hrow hagree hTcard
  exact ⟨p₀, p₁, hp₀, hp₁,
    selected_polynomials_align_of_canonical_gamma_baseZ_affine
      x₀ R hHyp hzeta N 131071 hN T root P hPdeg hspecializes hden
      hkF p₀ p₁ hp₀ hp₁ hgamma⟩

/-- Score-data form of the complete fixed-obstruction consumer.  Exact
generic-root status is derived internally from middle Hensel vanishing and
the selected factor's strict weighted support cap. -/
theorem fixed_obstruction_selected_pair_alignment_of_score_data_6400
    {F I : Type} [Field F] [Fintype F] [DecidableEq F]
    [Fintype I] [DecidableEq I]
    {H : F[X][Y]} [Fact (Irreducible H)] [Fact (0 < H.natDegree)]
    (omega : I ↪ F) (hn : Fintype.card I = 262144)
    (x₀ : F) (R : F[X][X][Y]) (N : ℕ) (hN : 131071 ≤ N)
    (hRirr : Irreducible R) (hRpos : 0 < R.natDegree)
    (hHyp : HenselNumerators.Hypotheses x₀ R H)
    (hzeta : HenselNumerators.zeta R x₀ H ≠ 0)
    (hYZ : YZCap R 1670075)
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
    (hTcard : 4031860 ≤ T.card)
    (hkF : 131071 < Fintype.card F) :
    ∃ p₀ p₁ : F[X], p₀.natDegree ≤ 131071 ∧
      p₁.natDegree ≤ 131071 ∧
      ∀ z : T, P z = p₀ + Polynomial.C (z : F) * p₁ := by
  have hroot := canonicalFunctionFieldGamma_is_root_of_score_data
    x₀ R hHyp hzeta N 131071 hN (by omega) hmiddle hweighted
  exact fixed_obstruction_selected_pair_alignment_6400 omega hn x₀ R N hN
    hRirr hRpos hHyp hzeta hYZ hroot T root P A U₀ U₁ hPdeg
    hspecializes hden hrow hagree hTcard hkF

end ProximityPrize.SubmissionLower
