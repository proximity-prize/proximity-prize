import ProximityPrize.SubmissionLower.BCHKSUniversalAffineObstruction
import ProximityPrize.SubmissionLower.BCHKSSelectedHenselData
import ProximityPrize.SubmissionLower.BCHKSSelectedNonpole
import ProximityPrize.SubmissionLower.BCHKSHenselBaseZAlignment

namespace ProximityPrize.SubmissionLower

open Polynomial Polynomial.Bivariate RationalFunctions
open RationalFunctions.HenselNumerators
open RationalFunctions.HenselNumerators.ConcreteFiniteNumerators

variable {F : Type} [Field F]

/-- A zero branch-independent affine obstruction forces the canonical Hensel
truncation to take the prescribed affine value at that coordinate. -/
theorem gamma_eval_eq_affine_of_universalAffineObstruction_eq_zero
    {H : F[X][Y]} [Fact (Irreducible H)] [Fact (0 < H.natDegree)]
    (x₀ x u₀ u₁ : F) (R : F[X][X][Y])
    (hHyp : HenselNumerators.Hypotheses x₀ R H)
    (hzeta : HenselNumerators.zeta R x₀ H ≠ 0)
    (N k : ℕ) (hkN : k ≤ N)
    (num : ℕ → F[X][Y]) (s : F[X][Y]) (E : ℕ)
    (hE : E = FiniteHenselWeight.denominatorExponent k)
    (hs : Polynomial.eval₂ (liftToFunctionField (H := H))
        (initialValue (H := H)) s = HenselNumerators.zeta R x₀ H)
    (hnum : ∀ i, i ≤ k →
      Polynomial.eval₂ (liftToFunctionField (H := H))
          (initialValue (H := H)) (num i) =
        finiteAlpha (R := R) (H := H) x₀ N i *
          HenselNumerators.zeta R x₀ H ^
            FiniteHenselWeight.denominatorExponent i)
    (hzero : Polynomial.eval₂ (liftToFunctionField (H := H))
      (initialValue (H := H))
        (universalAffineObstruction num s E k (x - x₀) u₀ u₁) = 0) :
    (canonicalFunctionFieldGamma H x₀ R N k).eval
        (fieldTo𝕃 (H := H) x) =
      fieldTo𝕃 (H := H) u₀ +
        liftToFunctionField (H := H) Polynomial.X *
          fieldTo𝕃 (H := H) u₁ := by
  let β := explicitBaseZGammaDifferenceRegular x₀ (x - x₀) u₀ u₁
    R hHyp hzeta N k hkN
  have hb0 : embeddingOf𝒪Into𝕃 H β = 0 := by
    rw [embedding_explicitBaseZGammaDifferenceRegular_eq_universalAffineObstruction
      x₀ (x - x₀) u₀ u₁ R hHyp hzeta N k hkN num s E hE hs hnum]
    rw [hzero]
    simp
  rw [embedding_explicitBaseZGammaDifferenceRegular x₀ (x - x₀)
    u₀ u₁ R hHyp hzeta N k hkN] at hb0
  have hdenfield : commonDenominator (R := R) (H := H) x₀ hHyp k ≠ 0 := by
    unfold commonDenominator
    exact mul_ne_zero (pow_ne_zero _ (Wfield_ne_zero (H := H)))
      (pow_ne_zero _ (by
        rw [etaField_eq]
        exact mul_ne_zero (pow_ne_zero _ (Wfield_ne_zero (H := H))) hzeta))
  have hdiff := (mul_eq_zero.mp hb0).resolve_right hdenfield
  rw [canonicalFunctionFieldGamma_eval]
  exact sub_eq_zero.mp hdiff



end ProximityPrize.SubmissionLower

namespace ProximityPrize.SubmissionLower

open Polynomial Polynomial.Bivariate RationalFunctions
open RationalFunctions.HenselNumerators
open RationalFunctions.HenselNumerators.ConcreteFiniteNumerators

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- The exact selected-pair fields consumed by universal alignment.  Unlike
`SelectedHenselData`, this package omits the legacy middle-range weight and
denominator ledgers, so it also supports an outer factor of Y-degree one. -/
structure UniversalSelectedHenselData
    (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [Fact (Irreducible H)] [Fact (0 < H.natDegree)]
    (hHyp : HenselNumerators.Hypotheses x₀ R H)
    (hzeta : HenselNumerators.zeta R x₀ H ≠ 0)
    (D d k DX : ℕ) (T : Finset F) (P : T → F[X]) where
  root : ∀ z : T, rationalRoot (monicize H) (z : F)
  hx : ∀ z : T, GoodAt (z : F) (root z) (fieldTo𝕃 (H := H) x₀) x₀
  hy : ∀ z : T, GoodAt (z : F) (root z)
    (initialValue (H := H)) ((P z).eval x₀)
  hsL : FiniteHensel.ySlope (liftedR (R := R) (H := H))
    (fieldTo𝕃 (H := H) x₀) (initialValue (H := H)) ≠ 0
  hsimple : ∀ z : T, FiniteHensel.IsSimpleRootAt
    (triSpecializeZ R (z : F)) x₀ ((P z).eval x₀)
  hExact : ∀ z : T, (triSpecializeZ R (z : F)).eval (P z) = 0
  hslope : ∀ z : T, GoodAt (z : F) (root z)
    (FiniteHensel.ySlope (liftedR (R := R) (H := H))
      (fieldTo𝕃 (H := H) x₀) (initialValue (H := H)))
    (FiniteHensel.ySlope (triSpecializeZ R (z : F)) x₀ ((P z).eval x₀))
  hW : ∀ z : T, H.leadingCoeff.eval (z : F) ≠ 0
  hxi : ∀ z : T, Polynomial.evalEval (z : F) (root z).1
    (HenselNumerators.xiPre x₀ R H) ≠ 0

/-- Forget the legacy-only fields of the old selected data package. -/
def SelectedHenselData.toUniversal
    {H : F[X][Y]} [Fact (Irreducible H)] [Fact (0 < H.natDegree)]
    {x₀ : F} {R : F[X][X][Y]}
    {hHyp : HenselNumerators.Hypotheses x₀ R H}
    {hzeta : HenselNumerators.zeta R x₀ H ≠ 0}
    {D d k DX : ℕ} {T : Finset F} {P : T → F[X]}
    (S : SelectedHenselData x₀ R H hHyp hzeta D d k DX T P) :
    UniversalSelectedHenselData x₀ R H hHyp hzeta D d k DX T P where
  root := S.root
  hx := S.hx
  hy := S.hy
  hsL := S.hsL
  hsimple := S.hsimple
  hExact := S.hExact
  hslope := S.hslope
  hW := S.hW
  hxi := S.hxi

/-- Selected-pair universal alignment core. The all-factor shell only has to
produce one selected Hensel pair and prove the branch-independent affine
obstruction vanishes at k+1 coordinates. No regular-weight or per-factor
root-counting hypothesis occurs in this consumer. -/
theorem universal_selected_pair_alignment_core
    {H : F[X][Y]} [Fact (Irreducible H)] [Fact (0 < H.natDegree)]
    (x₀ : F) (R : F[X][X][Y])
    (hHyp : HenselNumerators.Hypotheses x₀ R H)
    (hzeta : HenselNumerators.zeta R x₀ H ≠ 0)
    (D d k DX : ℕ) (hkDX : k < DX)
    (T : Finset F) (P : T → F[X])
    (S : SelectedHenselData x₀ R H hHyp hzeta D d k DX T P)
    (hNP : ∀ z : T, SelectedNonpoleData x₀ R H hHyp (z : F)
      (S.root z) x₀ ((P z).eval x₀))
    (hPdeg : ∀ z, (P z).natDegree ≤ k)
    (hkF : k < Fintype.card F)
    (A : Finset F) (hAcard : k + 1 ≤ A.card) (U₀ U₁ : F → F)
    (num : ℕ → F[X][Y]) (s : F[X][Y]) (E : ℕ)
    (hE : E = FiniteHenselWeight.denominatorExponent k)
    (hs : Polynomial.eval₂ (liftToFunctionField (H := H))
        (initialValue (H := H)) s = HenselNumerators.zeta R x₀ H)
    (hnum : ∀ i, i ≤ k →
      Polynomial.eval₂ (liftToFunctionField (H := H))
          (initialValue (H := H)) (num i) =
        finiteAlpha (R := R) (H := H) x₀ DX i *
          HenselNumerators.zeta R x₀ H ^
            FiniteHenselWeight.denominatorExponent i)
    (hzero : ∀ x ∈ A,
      Polynomial.eval₂ (liftToFunctionField (H := H))
        (initialValue (H := H))
          (universalAffineObstruction num s E k
            (x - x₀) (U₀ x) (U₁ x)) = 0) :
    ∃ p₀ p₁ : F[X], p₀.natDegree ≤ k ∧ p₁.natDegree ≤ k ∧
      ∀ z : T, P z = p₀ + Polynomial.C (z : F) * p₁ := by
  have hspecializes : ∀ z : T, ∀ n, n ≤ DX →
      concreteSpecializedAlpha x₀ R hHyp hzeta DX (z : F) (S.root z) n =
        FiniteHensel.TaylorCoeff (P z) x₀ n := by
    intro z n hn
    apply concreteSpecializedAlpha_eq_TaylorCoeff x₀ R hHyp hzeta DX
      (z : F) (S.root z) x₀ ((P z).eval x₀) (P z)
      (S.hx z) (S.hy z) S.hsL (S.hsimple z) rfl
      ((hPdeg z).trans (Nat.le_of_lt hkDX)) (S.hExact z) (S.hslope z)
      (S.hW z) (S.hxi z) n hn
  let γ := canonicalFunctionFieldGamma H x₀ R DX k
  have hγeval : ∀ x ∈ A, γ.eval (fieldTo𝕃 (H := H) x) =
      fieldTo𝕃 (H := H) (U₀ x) +
        liftToFunctionField (H := H) Polynomial.X *
          fieldTo𝕃 (H := H) (U₁ x) := by
    intro x hxA
    exact gamma_eval_eq_affine_of_universalAffineObstruction_eq_zero
      x₀ x (U₀ x) (U₁ x) R hHyp hzeta DX k
      (Nat.le_of_lt hkDX) num s E hE hs hnum (hzero x hxA)
  obtain ⟨p₀, p₁, hp₀, hp₁, hγ⟩ :=
    canonicalFunctionFieldGamma_baseZ_affine x₀ R DX k A hAcard
      U₀ U₁ (canonicalFunctionFieldGamma_natDegree_le x₀ R DX k) hγeval
  refine ⟨p₀, p₁, hp₀, hp₁, ?_⟩
  intro z
  let q := p₀ + Polynomial.C (z : F) * p₁
  apply Polynomial.eq_of_natDegree_lt_card_of_eval_eq (P z) q
    (f := fun x : F => x) Function.injective_id
  · intro x
    have hall : γ.eval (fieldTo𝕃 (H := H) x) =
        fieldTo𝕃 (H := H) (p₀.eval x) +
          liftToFunctionField (H := H) Polynomial.X *
            fieldTo𝕃 (H := H) (p₁.eval x) := by
      change (canonicalFunctionFieldGamma H x₀ R DX k).eval
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
    let β := explicitBaseZGammaDifferenceRegular x₀ (x - x₀)
      (p₀.eval x) (p₁.eval x) R hHyp hzeta DX k (Nat.le_of_lt hkDX)
    have hb0 : embeddingOf𝒪Into𝕃 H β = 0 := by
      rw [embedding_explicitBaseZGammaDifferenceRegular x₀ (x - x₀)
        (p₀.eval x) (p₁.eval x) R hHyp hzeta DX k
        (Nat.le_of_lt hkDX)]
      change (canonicalFunctionFieldGamma H x₀ R DX k).eval
        (fieldTo𝕃 (H := H) x) = _ at hall
      rw [canonicalFunctionFieldGamma_eval] at hall
      rw [hall]
      ring
    have hβzero : β = 0 := by
      apply embeddingOf𝒪Into𝕃_injective (Fact.out : 0 < H.natDegree)
      simpa using hb0
    have hpiz : piZ (z : F) (S.root z) β = 0 := by
      rw [hβzero]
      simp
    rw [piZ_explicitBaseZGammaDifferenceRegular_eq_zero_iff
      x₀ (x - x₀) (p₀.eval x) (p₁.eval x) (z : F) (S.root z)
      R hHyp hzeta DX k (Nat.le_of_lt hkDX) (P z) (hPdeg z)] at hpiz
    · simpa [q, sub_eq_add_neg, Polynomial.eval_add, Polynomial.eval_mul] using hpiz
    · intro i hi
      exact hspecializes z i (hi.trans (Nat.le_of_lt hkDX))
    · intro i _
      exact (hNP z).hden i
  · have hq : q.natDegree ≤ k := by
      exact (Polynomial.natDegree_add_le _ _).trans
        (max_le hp₀ ((Polynomial.natDegree_C_mul_le _ _).trans hp₁))
    exact max_lt ((hPdeg z).trans_lt hkF) (hq.trans_lt hkF)

theorem universal_selected_pair_alignment_core_light
    {H : F[X][Y]} [Fact (Irreducible H)] [Fact (0 < H.natDegree)]
    (x₀ : F) (R : F[X][X][Y])
    (hHyp : HenselNumerators.Hypotheses x₀ R H)
    (hzeta : HenselNumerators.zeta R x₀ H ≠ 0)
    (D d k DX : ℕ) (hkDX : k < DX)
    (T : Finset F) (P : T → F[X])
    (S : UniversalSelectedHenselData x₀ R H hHyp hzeta D d k DX T P)
    (hNP : ∀ z : T, SelectedNonpoleData x₀ R H hHyp (z : F)
      (S.root z) x₀ ((P z).eval x₀))
    (hPdeg : ∀ z, (P z).natDegree ≤ k)
    (hkF : k < Fintype.card F)
    (A : Finset F) (hAcard : k + 1 ≤ A.card) (U₀ U₁ : F → F)
    (num : ℕ → F[X][Y]) (s : F[X][Y]) (E : ℕ)
    (hE : E = FiniteHenselWeight.denominatorExponent k)
    (hs : Polynomial.eval₂ (liftToFunctionField (H := H))
        (initialValue (H := H)) s = HenselNumerators.zeta R x₀ H)
    (hnum : ∀ i, i ≤ k →
      Polynomial.eval₂ (liftToFunctionField (H := H))
          (initialValue (H := H)) (num i) =
        finiteAlpha (R := R) (H := H) x₀ DX i *
          HenselNumerators.zeta R x₀ H ^
            FiniteHenselWeight.denominatorExponent i)
    (hzero : ∀ x ∈ A,
      Polynomial.eval₂ (liftToFunctionField (H := H))
        (initialValue (H := H))
          (universalAffineObstruction num s E k
            (x - x₀) (U₀ x) (U₁ x)) = 0) :
    ∃ p₀ p₁ : F[X], p₀.natDegree ≤ k ∧ p₁.natDegree ≤ k ∧
      ∀ z : T, P z = p₀ + Polynomial.C (z : F) * p₁ := by
  have hspecializes : ∀ z : T, ∀ n, n ≤ DX →
      concreteSpecializedAlpha x₀ R hHyp hzeta DX (z : F) (S.root z) n =
        FiniteHensel.TaylorCoeff (P z) x₀ n := by
    intro z n hn
    apply concreteSpecializedAlpha_eq_TaylorCoeff x₀ R hHyp hzeta DX
      (z : F) (S.root z) x₀ ((P z).eval x₀) (P z)
      (S.hx z) (S.hy z) S.hsL (S.hsimple z) rfl
      ((hPdeg z).trans (Nat.le_of_lt hkDX)) (S.hExact z) (S.hslope z)
      (S.hW z) (S.hxi z) n hn
  let γ := canonicalFunctionFieldGamma H x₀ R DX k
  have hγeval : ∀ x ∈ A, γ.eval (fieldTo𝕃 (H := H) x) =
      fieldTo𝕃 (H := H) (U₀ x) +
        liftToFunctionField (H := H) Polynomial.X *
          fieldTo𝕃 (H := H) (U₁ x) := by
    intro x hxA
    exact gamma_eval_eq_affine_of_universalAffineObstruction_eq_zero
      x₀ x (U₀ x) (U₁ x) R hHyp hzeta DX k
      (Nat.le_of_lt hkDX) num s E hE hs hnum (hzero x hxA)
  obtain ⟨p₀, p₁, hp₀, hp₁, hγ⟩ :=
    canonicalFunctionFieldGamma_baseZ_affine x₀ R DX k A hAcard
      U₀ U₁ (canonicalFunctionFieldGamma_natDegree_le x₀ R DX k) hγeval
  refine ⟨p₀, p₁, hp₀, hp₁, ?_⟩
  intro z
  let q := p₀ + Polynomial.C (z : F) * p₁
  apply Polynomial.eq_of_natDegree_lt_card_of_eval_eq (P z) q
    (f := fun x : F => x) Function.injective_id
  · intro x
    have hall : γ.eval (fieldTo𝕃 (H := H) x) =
        fieldTo𝕃 (H := H) (p₀.eval x) +
          liftToFunctionField (H := H) Polynomial.X *
            fieldTo𝕃 (H := H) (p₁.eval x) := by
      change (canonicalFunctionFieldGamma H x₀ R DX k).eval
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
    let β := explicitBaseZGammaDifferenceRegular x₀ (x - x₀)
      (p₀.eval x) (p₁.eval x) R hHyp hzeta DX k (Nat.le_of_lt hkDX)
    have hb0 : embeddingOf𝒪Into𝕃 H β = 0 := by
      rw [embedding_explicitBaseZGammaDifferenceRegular x₀ (x - x₀)
        (p₀.eval x) (p₁.eval x) R hHyp hzeta DX k
        (Nat.le_of_lt hkDX)]
      change (canonicalFunctionFieldGamma H x₀ R DX k).eval
        (fieldTo𝕃 (H := H) x) = _ at hall
      rw [canonicalFunctionFieldGamma_eval] at hall
      rw [hall]
      ring
    have hβzero : β = 0 := by
      apply embeddingOf𝒪Into𝕃_injective (Fact.out : 0 < H.natDegree)
      simpa using hb0
    have hpiz : piZ (z : F) (S.root z) β = 0 := by
      rw [hβzero]
      simp
    rw [piZ_explicitBaseZGammaDifferenceRegular_eq_zero_iff
      x₀ (x - x₀) (p₀.eval x) (p₁.eval x) (z : F) (S.root z)
      R hHyp hzeta DX k (Nat.le_of_lt hkDX) (P z) (hPdeg z)] at hpiz
    · simpa [q, sub_eq_add_neg, Polynomial.eval_add, Polynomial.eval_mul] using hpiz
    · intro i hi
      exact hspecializes z i (hi.trans (Nat.le_of_lt hkDX))
    · intro i _
      exact (hNP z).hden i
  · have hq : q.natDegree ≤ k := by
      exact (Polynomial.natDegree_add_le _ _).trans
        (max_le hp₀ ((Polynomial.natDegree_C_mul_le _ _).trans hp₁))
    exact max_lt ((hPdeg z).trans_lt hkF) (hq.trans_lt hkF)

end ProximityPrize.SubmissionLower
