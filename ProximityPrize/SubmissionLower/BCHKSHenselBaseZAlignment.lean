import ProximityPrize.SubmissionLower.BCHKSBaseZAffine

namespace ProximityPrize.SubmissionLower
open Polynomial Polynomial.Bivariate RationalFunctions
open RationalFunctions.HenselNumerators
open RationalFunctions.HenselNumerators.ConcreteFiniteNumerators

variable {F : Type} [Field F]

/-- Evaluation of the canonical centered lift is the corresponding evaluated
finite Hensel truncation.  This is the normalization used by the selected-data
alignment argument. -/
theorem canonicalFunctionFieldGamma_eval
    {H : F[X][Y]} [Fact (Irreducible H)] [Fact (0 < H.natDegree)]
    (x₀ x : F) (R : F[X][X][Y]) (N k : ℕ) :
    (canonicalFunctionFieldGamma H x₀ R N k).eval (fieldTo𝕃 (H:=H) x) =
      evaluatedFiniteAlpha (R:=R) (H:=H) x₀ (x-x₀) N k := by
  unfold canonicalFunctionFieldGamma evaluatedFiniteAlpha
  rw [Polynomial.eval_comp]
  unfold FiniteHensel.truncSeries
  simp only [Polynomial.eval_finset_sum, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_X]
  simp [fieldTo𝕃, map_sub]

/-- The canonical centered lift has degree at most its truncation order. -/
theorem canonicalFunctionFieldGamma_natDegree_le
    {H : F[X][Y]} [Fact (Irreducible H)] [Fact (0 < H.natDegree)]
    (x₀ : F) (R : F[X][X][Y]) (N k : ℕ) :
    (canonicalFunctionFieldGamma H x₀ R N k).natDegree ≤ k := by
  unfold canonicalFunctionFieldGamma
  have ht : (FiniteHensel.truncSeries
      (finiteAlpha (R:=R) (H:=H) x₀ N) k).natDegree ≤ k := by
    unfold FiniteHensel.truncSeries
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro i hi
    rw [Finset.mem_range] at hi
    exact (Polynomial.natDegree_C_mul_le _ _).trans
      (Polynomial.natDegree_pow_le.trans (by simp; omega))
  calc
    _ ≤ (FiniteHensel.truncSeries (finiteAlpha (R:=R) (H:=H) x₀ N) k).natDegree *
        (Polynomial.X - Polynomial.C (fieldTo𝕃 (H:=H) x₀)).natDegree :=
      Polynomial.natDegree_comp_le
    _ ≤ k := by rw [Polynomial.natDegree_X_sub_C, Nat.mul_one]; exact ht

end ProximityPrize.SubmissionLower


namespace ProximityPrize.SubmissionLower
open Polynomial Polynomial.Bivariate RationalFunctions
open RationalFunctions.HenselNumerators
open RationalFunctions.HenselNumerators.ConcreteFiniteNumerators

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- Final selected-data alignment theorem, using the canonical finite-Hensel lift. -/
theorem hensel_baseZ_alignment_final
    {H : F[X][Y]} [Fact (Irreducible H)] [Fact (0 < H.natDegree)]
    (x₀ : F) (R : F[X][X][Y])
    (hHyp : HenselNumerators.Hypotheses x₀ R H)
    (hzeta : HenselNumerators.zeta R x₀ H ≠ 0)
    (D d k DX e : ℕ) (hkDX : k < DX)
    (hHD : Bivariate.totalDegree H ≤ D)
    (hRD : YZCap R D)
    (hRdeg : 2 ≤ Bivariate.natDegreeY R)
    (T : Finset F) (root : ∀ z : T, rationalRoot (monicize H) (z:F))
    (P : T → F[X]) (hPdeg : ∀ z, (P z).natDegree ≤ k)
    (hx : ∀ z : T, GoodAt (z:F) (root z) (fieldTo𝕃 (H:=H) x₀) x₀)
    (hy : ∀ z : T, GoodAt (z:F) (root z) (initialValue (H:=H)) ((P z).eval x₀))
    (hsL : FiniteHensel.ySlope (liftedR (R:=R) (H:=H))
      (fieldTo𝕃 (H:=H) x₀) (initialValue (H:=H)) ≠ 0)
    (hsimple : ∀ z : T, FiniteHensel.IsSimpleRootAt
      (triSpecializeZ R (z:F)) x₀ ((P z).eval x₀))
    (hExact : ∀ z : T, (triSpecializeZ R (z:F)).eval (P z) = 0)
    (hslope : ∀ z : T, GoodAt (z:F) (root z)
      (FiniteHensel.ySlope (liftedR (R:=R) (H:=H))
        (fieldTo𝕃 (H:=H) x₀) (initialValue (H:=H)))
      (FiniteHensel.ySlope (triSpecializeZ R (z:F)) x₀ ((P z).eval x₀)))
    (hW : ∀ z : T, H.leadingCoeff.eval (z:F) ≠ 0)
    (hxi : ∀ z : T, Polynomial.evalEval (z:F) (root z).1
      (HenselNumerators.xiPre x₀ R H) ≠ 0)
    (hden : ∀ t, t < DX → ∀ z : T,
      piZ (z:F) (root z) (concreteDenRegularBridge x₀ R hHyp t) ≠ 0)
    (hweight : ∀ t, k < t → t < DX →
      regularWeight (Fact.out : 0 < H.natDegree)
        (concreteBetaUpTo x₀ R hHyp hzeta DX t) D ≤
          (WithBot.some ((2*t+1)*d*D) : WithBot ℕ))
    (hcard : 2*DX*H.natDegree*d*D + e + 1 < T.card)
    (hkF : k < Fintype.card F)
    (A : Finset F) (hAcard : k+1 ≤ A.card) (U₀ U₁ : F → F)
    (Fib : A → Finset T)
    (hFibcard : ∀ x : A,
      (2*k+2)*Bivariate.natDegreeY R*D*H.natDegree < (Fib x).card)
    (hagree : ∀ x : A, ∀ z ∈ Fib x,
      (P z).eval (x:F) = U₀ x + (z:F) * U₁ x) :
    (∀ t, k < t → t < DX → finiteAlpha (R:=R) (H:=H) x₀ DX t = 0) ∧
    ∃ p₀ p₁ : F[X], p₀.natDegree ≤ k ∧ p₁.natDegree ≤ k ∧
      ∀ z : T, P z = p₀ + Polynomial.C (z:F) * p₁ := by
  have hspecializes : ∀ z : T, ∀ n, n ≤ DX →
      concreteSpecializedAlpha x₀ R hHyp hzeta DX (z:F) (root z) n =
        FiniteHensel.TaylorCoeff (P z) x₀ n := by
    intro z n hn
    apply concreteSpecializedAlpha_eq_TaylorCoeff x₀ R hHyp hzeta DX
      (z:F) (root z) x₀ ((P z).eval x₀) (P z)
      (hx z) (hy z) hsL (hsimple z) rfl
      (hPdeg z |>.trans (Nat.le_of_lt hkDX)) (hExact z) (hslope z) (hW z) (hxi z) n hn
  have hmiddle : ∀ t, k < t → t < DX →
      finiteAlpha (R:=R) (H:=H) x₀ DX t = 0 := by
    apply concreteFiniteAlpha_middle_vanish_regularDen x₀ R hHyp hzeta
      D d k DX e hHD T root P (fun _ => x₀) hPdeg hspecializes
    · intro t _ ht z; exact hden t ht z
    · exact hweight
    · exact hcard
  refine ⟨hmiddle, ?_⟩
  let γ := canonicalFunctionFieldGamma H x₀ R DX k
  have hγeval : ∀ x ∈ A, γ.eval (fieldTo𝕃 (H:=H) x) =
      fieldTo𝕃 (H:=H) (U₀ x) + liftToFunctionField (H:=H) Polynomial.X * fieldTo𝕃 (H:=H) (U₁ x) := by
    intro x hxA
    let β := explicitBaseZGammaDifferenceRegular x₀ (x-x₀) (U₀ x) (U₁ x)
      R hHyp hzeta DX k (Nat.le_of_lt hkDX)
    have hpi : ∀ z ∈ Fib ⟨x,hxA⟩, piZ (z:F) (root z) β = 0 := by
      intro z hz
      rw [piZ_explicitBaseZGammaDifferenceRegular_eq_zero_iff
        x₀ (x-x₀) (U₀ x) (U₁ x) (z:F) (root z)
        R hHyp hzeta DX k (Nat.le_of_lt hkDX) (P z) (hPdeg z)]
      · simpa [sub_eq_add_neg, add_assoc] using hagree ⟨x,hxA⟩ z hz
      · intro i hi; exact hspecializes z i (hi.trans (Nat.le_of_lt hkDX))
      · intro i hi; exact hden i (hi.trans_lt hkDX) z
    have hsub : (↑(Fib ⟨x,hxA⟩) : Set T) ⊆
        {z | (z:F) ∈ rationalVanishingSet β} := by
      intro z hz
      exact ⟨root z, hpi z hz⟩
    let B : Finset F := (Fib ⟨x,hxA⟩).image (fun z : T => (z:F))
    have hBcard : B.card = (Fib ⟨x,hxA⟩).card := by
      apply Finset.card_image_iff.mpr
      intro a _ b _ hab
      exact Subtype.ext hab
    have hBsub : (↑B : Set F) ⊆ rationalVanishingSet β := by
      intro z hz
      rw [Finset.mem_coe, Finset.mem_image] at hz
      obtain ⟨w, hw, rfl⟩ := hz
      exact ⟨root w, hpi w hw⟩
    have hsetcard : (Fib ⟨x,hxA⟩).card ≤ Set.ncard (rationalVanishingSet β) := by
      rw [← hBcard, ← Set.ncard_coe_finset B]
      exact Set.ncard_le_ncard hBsub
    have hwβ := ProximityPrize.SubmissionLower.explicitBaseZGammaDifferenceRegular_weight x₀ (x-x₀)
      (U₀ x) (U₁ x) R hHyp hzeta (Fact.out : 0 < H.natDegree) hHD hRD hRdeg
      DX k (Nat.le_of_lt hkDX)
    have hncard : regularWeight (Fact.out : 0 < H.natDegree) β D * H.natDegree <
        Set.ncard (rationalVanishingSet β) := by
      cases hw : regularWeight (Fact.out : 0 < H.natDegree) β D with
      | bot => simp [Nat.ne_of_gt (Fact.out : 0 < H.natDegree)]
      | coe w =>
        rw [hw] at hwβ
        change ((w * H.natDegree : ℕ) : WithBot ℕ) < _
        exact WithBot.coe_lt_coe.mpr ((Nat.mul_le_mul_right H.natDegree
          (WithBot.coe_le_coe.mp hwβ)).trans_lt ((hFibcard ⟨x,hxA⟩).trans_le hsetcard))
    have hb0 := embedding_eq_zero_of_many_rational_roots
      (Fact.out : 0 < H.natDegree) β D hHD hncard
    rw [embedding_explicitBaseZGammaDifferenceRegular x₀ (x-x₀)
      (U₀ x) (U₁ x) R hHyp hzeta DX k (Nat.le_of_lt hkDX)] at hb0
    have hdenfield : commonDenominator (R:=R) (H:=H) x₀ hHyp k ≠ 0 := by
      unfold commonDenominator
      exact mul_ne_zero (pow_ne_zero _ (Wfield_ne_zero (H:=H)))
        (pow_ne_zero _ (by
          rw [etaField_eq]
          exact mul_ne_zero (pow_ne_zero _ (Wfield_ne_zero (H:=H))) hzeta))
    have hdiff := (mul_eq_zero.mp hb0).resolve_right hdenfield
    rw [canonicalFunctionFieldGamma_eval]
    exact sub_eq_zero.mp hdiff
  obtain ⟨p₀,p₁,hp₀,hp₁,hγ⟩ := canonicalFunctionFieldGamma_baseZ_affine x₀ R DX k A hAcard
    U₀ U₁ (canonicalFunctionFieldGamma_natDegree_le x₀ R DX k) hγeval
  refine ⟨p₀,p₁,hp₀,hp₁,?_⟩
  intro z
  let q := p₀ + Polynomial.C (z:F) * p₁
  apply Polynomial.eq_of_natDegree_lt_card_of_eval_eq (P z) q
    (f := fun x : F => x) Function.injective_id
  · intro x
    have hall : γ.eval (fieldTo𝕃 (H:=H) x) =
        fieldTo𝕃 (H:=H) (p₀.eval x) + liftToFunctionField (H:=H) Polynomial.X *
          fieldTo𝕃 (H:=H) (p₁.eval x) := by
      change (canonicalFunctionFieldGamma H x₀ R DX k).eval
        (fieldTo𝕃 (H:=H) x) = _
      rw [hγ]
      simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_map]
      have hp0map : Polynomial.eval₂ (liftToFunctionField (H:=H) |>.comp Polynomial.C)
          (liftToFunctionField (H:=H) (Polynomial.C x)) p₀ =
          liftToFunctionField (H:=H) (Polynomial.C (p₀.eval x)) := by
        rw [← Polynomial.hom_eval₂ p₀ Polynomial.C (liftToFunctionField (H:=H))
          (Polynomial.C x)]
        simp
      have hp1map : Polynomial.eval₂ (liftToFunctionField (H:=H) |>.comp Polynomial.C)
          (liftToFunctionField (H:=H) (Polynomial.C x)) p₁ =
          liftToFunctionField (H:=H) (Polynomial.C (p₁.eval x)) := by
        rw [← Polynomial.hom_eval₂ p₁ Polynomial.C (liftToFunctionField (H:=H))
          (Polynomial.C x)]
        simp
      change Polynomial.eval₂ (liftToFunctionField (H:=H) |>.comp Polynomial.C)
          (liftToFunctionField (H:=H) (Polynomial.C x)) p₀ + liftToFunctionField (H:=H) Polynomial.X *
          Polynomial.eval₂ (liftToFunctionField (H:=H) |>.comp Polynomial.C)
            (liftToFunctionField (H:=H) (Polynomial.C x)) p₁ = _
      rw [hp0map, hp1map]
      rfl
    let β := explicitBaseZGammaDifferenceRegular x₀ (x-x₀)
      (p₀.eval x) (p₁.eval x) R hHyp hzeta DX k (Nat.le_of_lt hkDX)
    have hb0 : embeddingOf𝒪Into𝕃 H β = 0 := by
      rw [embedding_explicitBaseZGammaDifferenceRegular x₀ (x-x₀)
        (p₀.eval x) (p₁.eval x) R hHyp hzeta DX k (Nat.le_of_lt hkDX)]
      change (canonicalFunctionFieldGamma H x₀ R DX k).eval (fieldTo𝕃 (H:=H) x) = _ at hall
      rw [canonicalFunctionFieldGamma_eval] at hall
      rw [hall]
      ring
    have hβzero : β = 0 := by
      apply embeddingOf𝒪Into𝕃_injective (Fact.out : 0 < H.natDegree)
      simpa using hb0
    have hpiz : piZ (z:F) (root z) β = 0 := by
      rw [hβzero]
      simp
    rw [piZ_explicitBaseZGammaDifferenceRegular_eq_zero_iff
      x₀ (x-x₀) (p₀.eval x) (p₁.eval x) (z:F) (root z)
      R hHyp hzeta DX k (Nat.le_of_lt hkDX)
      (P z) (hPdeg z)] at hpiz
    · simpa [q, sub_eq_add_neg, Polynomial.eval_add, Polynomial.eval_mul] using hpiz
    · intro i hi; exact hspecializes z i (hi.trans (Nat.le_of_lt hkDX))
    · intro i hi; exact hden i (hi.trans_lt hkDX) z
  · have hq : q.natDegree ≤ k := by
      exact (Polynomial.natDegree_add_le _ _).trans
        (max_le hp₀ ((Polynomial.natDegree_C_mul_le _ _).trans hp₁))
    exact max_lt ((hPdeg z).trans_lt hkF) (hq.trans_lt hkF)


theorem hensel_baseZ_alignment_final_exact_yz
    {H : F[X][Y]} [Fact (Irreducible H)] [Fact (0 < H.natDegree)]
    (x₀ : F) (R : F[X][X][Y])
    (hHyp : HenselNumerators.Hypotheses x₀ R H)
    (hzeta : HenselNumerators.zeta R x₀ H ≠ 0)
    (D d k DX e : ℕ) (hkDX : k < DX)
    (hHD : Bivariate.totalDegree H ≤ D)
    (hRD : YZCap R D)
    (hRdeg : 2 ≤ Bivariate.natDegreeY R)
    (T : Finset F) (root : ∀ z : T, rationalRoot (monicize H) (z:F))
    (P : T → F[X]) (hPdeg : ∀ z, (P z).natDegree ≤ k)
    (hx : ∀ z : T, GoodAt (z:F) (root z) (fieldTo𝕃 (H:=H) x₀) x₀)
    (hy : ∀ z : T, GoodAt (z:F) (root z) (initialValue (H:=H)) ((P z).eval x₀))
    (hsL : FiniteHensel.ySlope (liftedR (R:=R) (H:=H))
      (fieldTo𝕃 (H:=H) x₀) (initialValue (H:=H)) ≠ 0)
    (hsimple : ∀ z : T, FiniteHensel.IsSimpleRootAt
      (triSpecializeZ R (z:F)) x₀ ((P z).eval x₀))
    (hExact : ∀ z : T, (triSpecializeZ R (z:F)).eval (P z) = 0)
    (hslope : ∀ z : T, GoodAt (z:F) (root z)
      (FiniteHensel.ySlope (liftedR (R:=R) (H:=H))
        (fieldTo𝕃 (H:=H) x₀) (initialValue (H:=H)))
      (FiniteHensel.ySlope (triSpecializeZ R (z:F)) x₀ ((P z).eval x₀)))
    (hW : ∀ z : T, H.leadingCoeff.eval (z:F) ≠ 0)
    (hxi : ∀ z : T, Polynomial.evalEval (z:F) (root z).1
      (HenselNumerators.xiPre x₀ R H) ≠ 0)
    (hden : ∀ t, t < DX → ∀ z : T,
      piZ (z:F) (root z) (concreteDenRegularBridge x₀ R hHyp t) ≠ 0)
    (hweight : ∀ t, k < t → t < DX →
      regularWeight (Fact.out : 0 < H.natDegree)
        (concreteBetaUpTo x₀ R hHyp hzeta DX t) D ≤
          (WithBot.some ((2*t+1)*d*D) : WithBot ℕ))
    (hcard : 2*DX*H.natDegree*d*D + e + 1 < T.card)
    (hkF : k < Fintype.card F)
    (A : Finset F) (hAcard : k+1 ≤ A.card) (U₀ U₁ : F → F)
    (Fib : A → Finset T)
    (hFibcard : ∀ x : A,
      (((2*k+1)*Bivariate.natDegreeY R*D)+1)*H.natDegree < (Fib x).card)
    (hagree : ∀ x : A, ∀ z ∈ Fib x,
      (P z).eval (x:F) = U₀ x + (z:F) * U₁ x) :
    (∀ t, k < t → t < DX → finiteAlpha (R:=R) (H:=H) x₀ DX t = 0) ∧
    ∃ p₀ p₁ : F[X], p₀.natDegree ≤ k ∧ p₁.natDegree ≤ k ∧
      ∀ z : T, P z = p₀ + Polynomial.C (z:F) * p₁ := by
  have hspecializes : ∀ z : T, ∀ n, n ≤ DX →
      concreteSpecializedAlpha x₀ R hHyp hzeta DX (z:F) (root z) n =
        FiniteHensel.TaylorCoeff (P z) x₀ n := by
    intro z n hn
    apply concreteSpecializedAlpha_eq_TaylorCoeff x₀ R hHyp hzeta DX
      (z:F) (root z) x₀ ((P z).eval x₀) (P z)
      (hx z) (hy z) hsL (hsimple z) rfl
      (hPdeg z |>.trans (Nat.le_of_lt hkDX)) (hExact z) (hslope z) (hW z) (hxi z) n hn
  have hmiddle : ∀ t, k < t → t < DX →
      finiteAlpha (R:=R) (H:=H) x₀ DX t = 0 := by
    apply concreteFiniteAlpha_middle_vanish_regularDen x₀ R hHyp hzeta
      D d k DX e hHD T root P (fun _ => x₀) hPdeg hspecializes
    · intro t _ ht z; exact hden t ht z
    · exact hweight
    · exact hcard
  refine ⟨hmiddle, ?_⟩
  let γ := canonicalFunctionFieldGamma H x₀ R DX k
  have hγeval : ∀ x ∈ A, γ.eval (fieldTo𝕃 (H:=H) x) =
      fieldTo𝕃 (H:=H) (U₀ x) + liftToFunctionField (H:=H) Polynomial.X * fieldTo𝕃 (H:=H) (U₁ x) := by
    intro x hxA
    let β := explicitBaseZGammaDifferenceRegular x₀ (x-x₀) (U₀ x) (U₁ x)
      R hHyp hzeta DX k (Nat.le_of_lt hkDX)
    have hpi : ∀ z ∈ Fib ⟨x,hxA⟩, piZ (z:F) (root z) β = 0 := by
      intro z hz
      rw [piZ_explicitBaseZGammaDifferenceRegular_eq_zero_iff
        x₀ (x-x₀) (U₀ x) (U₁ x) (z:F) (root z)
        R hHyp hzeta DX k (Nat.le_of_lt hkDX) (P z) (hPdeg z)]
      · simpa [sub_eq_add_neg, add_assoc] using hagree ⟨x,hxA⟩ z hz
      · intro i hi; exact hspecializes z i (hi.trans (Nat.le_of_lt hkDX))
      · intro i hi; exact hden i (hi.trans_lt hkDX) z
    have hsub : (↑(Fib ⟨x,hxA⟩) : Set T) ⊆
        {z | (z:F) ∈ rationalVanishingSet β} := by
      intro z hz
      exact ⟨root z, hpi z hz⟩
    let B : Finset F := (Fib ⟨x,hxA⟩).image (fun z : T => (z:F))
    have hBcard : B.card = (Fib ⟨x,hxA⟩).card := by
      apply Finset.card_image_iff.mpr
      intro a _ b _ hab
      exact Subtype.ext hab
    have hBsub : (↑B : Set F) ⊆ rationalVanishingSet β := by
      intro z hz
      rw [Finset.mem_coe, Finset.mem_image] at hz
      obtain ⟨w, hw, rfl⟩ := hz
      exact ⟨root w, hpi w hw⟩
    have hsetcard : (Fib ⟨x,hxA⟩).card ≤ Set.ncard (rationalVanishingSet β) := by
      rw [← hBcard, ← Set.ncard_coe_finset B]
      exact Set.ncard_le_ncard hBsub
    have hwβ := ProximityPrize.SubmissionLower.explicitBaseZGammaDifferenceRegular_weight_exact x₀ (x-x₀)
      (U₀ x) (U₁ x) R hHyp hzeta (Fact.out : 0 < H.natDegree) hHD hRD hRdeg
      DX k (Nat.le_of_lt hkDX)
    have hncard : regularWeight (Fact.out : 0 < H.natDegree) β D * H.natDegree <
        Set.ncard (rationalVanishingSet β) := by
      cases hw : regularWeight (Fact.out : 0 < H.natDegree) β D with
      | bot => simp [Nat.ne_of_gt (Fact.out : 0 < H.natDegree)]
      | coe w =>
        rw [hw] at hwβ
        change ((w * H.natDegree : ℕ) : WithBot ℕ) < _
        exact WithBot.coe_lt_coe.mpr ((Nat.mul_le_mul_right H.natDegree
          (WithBot.coe_le_coe.mp hwβ)).trans_lt ((hFibcard ⟨x,hxA⟩).trans_le hsetcard))
    have hb0 := embedding_eq_zero_of_many_rational_roots
      (Fact.out : 0 < H.natDegree) β D hHD hncard
    rw [embedding_explicitBaseZGammaDifferenceRegular x₀ (x-x₀)
      (U₀ x) (U₁ x) R hHyp hzeta DX k (Nat.le_of_lt hkDX)] at hb0
    have hdenfield : commonDenominator (R:=R) (H:=H) x₀ hHyp k ≠ 0 := by
      unfold commonDenominator
      exact mul_ne_zero (pow_ne_zero _ (Wfield_ne_zero (H:=H)))
        (pow_ne_zero _ (by
          rw [etaField_eq]
          exact mul_ne_zero (pow_ne_zero _ (Wfield_ne_zero (H:=H))) hzeta))
    have hdiff := (mul_eq_zero.mp hb0).resolve_right hdenfield
    rw [canonicalFunctionFieldGamma_eval]
    exact sub_eq_zero.mp hdiff
  obtain ⟨p₀,p₁,hp₀,hp₁,hγ⟩ := canonicalFunctionFieldGamma_baseZ_affine x₀ R DX k A hAcard
    U₀ U₁ (canonicalFunctionFieldGamma_natDegree_le x₀ R DX k) hγeval
  refine ⟨p₀,p₁,hp₀,hp₁,?_⟩
  intro z
  let q := p₀ + Polynomial.C (z:F) * p₁
  apply Polynomial.eq_of_natDegree_lt_card_of_eval_eq (P z) q
    (f := fun x : F => x) Function.injective_id
  · intro x
    have hall : γ.eval (fieldTo𝕃 (H:=H) x) =
        fieldTo𝕃 (H:=H) (p₀.eval x) + liftToFunctionField (H:=H) Polynomial.X *
          fieldTo𝕃 (H:=H) (p₁.eval x) := by
      change (canonicalFunctionFieldGamma H x₀ R DX k).eval
        (fieldTo𝕃 (H:=H) x) = _
      rw [hγ]
      simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_map]
      have hp0map : Polynomial.eval₂ (liftToFunctionField (H:=H) |>.comp Polynomial.C)
          (liftToFunctionField (H:=H) (Polynomial.C x)) p₀ =
          liftToFunctionField (H:=H) (Polynomial.C (p₀.eval x)) := by
        rw [← Polynomial.hom_eval₂ p₀ Polynomial.C (liftToFunctionField (H:=H))
          (Polynomial.C x)]
        simp
      have hp1map : Polynomial.eval₂ (liftToFunctionField (H:=H) |>.comp Polynomial.C)
          (liftToFunctionField (H:=H) (Polynomial.C x)) p₁ =
          liftToFunctionField (H:=H) (Polynomial.C (p₁.eval x)) := by
        rw [← Polynomial.hom_eval₂ p₁ Polynomial.C (liftToFunctionField (H:=H))
          (Polynomial.C x)]
        simp
      change Polynomial.eval₂ (liftToFunctionField (H:=H) |>.comp Polynomial.C)
          (liftToFunctionField (H:=H) (Polynomial.C x)) p₀ + liftToFunctionField (H:=H) Polynomial.X *
          Polynomial.eval₂ (liftToFunctionField (H:=H) |>.comp Polynomial.C)
            (liftToFunctionField (H:=H) (Polynomial.C x)) p₁ = _
      rw [hp0map, hp1map]
      rfl
    let β := explicitBaseZGammaDifferenceRegular x₀ (x-x₀)
      (p₀.eval x) (p₁.eval x) R hHyp hzeta DX k (Nat.le_of_lt hkDX)
    have hb0 : embeddingOf𝒪Into𝕃 H β = 0 := by
      rw [embedding_explicitBaseZGammaDifferenceRegular x₀ (x-x₀)
        (p₀.eval x) (p₁.eval x) R hHyp hzeta DX k (Nat.le_of_lt hkDX)]
      change (canonicalFunctionFieldGamma H x₀ R DX k).eval (fieldTo𝕃 (H:=H) x) = _ at hall
      rw [canonicalFunctionFieldGamma_eval] at hall
      rw [hall]
      ring
    have hβzero : β = 0 := by
      apply embeddingOf𝒪Into𝕃_injective (Fact.out : 0 < H.natDegree)
      simpa using hb0
    have hpiz : piZ (z:F) (root z) β = 0 := by
      rw [hβzero]
      simp
    rw [piZ_explicitBaseZGammaDifferenceRegular_eq_zero_iff
      x₀ (x-x₀) (p₀.eval x) (p₁.eval x) (z:F) (root z)
      R hHyp hzeta DX k (Nat.le_of_lt hkDX)
      (P z) (hPdeg z)] at hpiz
    · simpa [q, sub_eq_add_neg, Polynomial.eval_add, Polynomial.eval_mul] using hpiz
    · intro i hi; exact hspecializes z i (hi.trans (Nat.le_of_lt hkDX))
    · intro i hi; exact hden i (hi.trans_lt hkDX) z
  · have hq : q.natDegree ≤ k := by
      exact (Polynomial.natDegree_add_le _ _).trans
        (max_le hp₀ ((Polynomial.natDegree_C_mul_le _ _).trans hp₁))
    exact max_lt ((hPdeg z).trans_lt hkF) (hq.trans_lt hkF)


end ProximityPrize.SubmissionLower
