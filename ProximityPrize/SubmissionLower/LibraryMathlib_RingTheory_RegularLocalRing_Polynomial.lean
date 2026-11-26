import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.LibraryMathlib_RingTheory_Ideal_MonicSpan
import ProximityPrize.SubmissionLower.LibraryMathlib_RingTheory_KrullDimension_Polynomial
set_option Elab.async false
/-
Copyright (c) 2025 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/







/-!
# Polynomial over Regular Ring

In this file we prove that the polynomial ring over a regular ring is regular.

## Main results

* `Polynomial.isRegularRing_of_isRegularRing` : the polynomial ring over a regular ring is
  a regular ring.

* `MvPolynomial.isRegularRing_of_isRegularRing` : the multivariate polynomial ring with finite
  variates over a regular ring is a regular ring.
-/

section

variable (R : Type*) [CommRing R]

open IsLocalRing Polynomial Ideal

lemma Polynomial.isRegularLocalRing_localization_atPrime_of_comap_eq_maximalIdeal
    [IsRegularLocalRing R] (p : Ideal (Polynomial R)) [p.IsPrime] (max : p.comap C = maximalIdeal R) :
    IsRegularLocalRing (Localization.AtPrime p) := by
  apply IsRegularLocalRing.of_spanFinrank_maximalIdeal_le
  let q := (maximalIdeal R).map C
  have qle : q ≤ p := by simpa [q, ← max] using map_comap_le
  have reg := (isRegularLocalRing_iff R).mp ‹_›
  have fg' := (maximalIdeal R).fg_of_isNoetherianRing
  have fg := Submodule.FG.finite_generators fg'
  have ht : (maximalIdeal R).height ≤ q.height := le_of_eq (height_map_C (maximalIdeal R)).symm
  by_cases eq : p = q
  · have ht1 : (maximalIdeal R).height ≤ p.height := by simpa [eq]
    have : Ideal.span ((algebraMap R (Localization.AtPrime p)) '' (maximalIdeal R).generators) =
      maximalIdeal (Localization.AtPrime p) := by
      rw [IsScalarTower.algebraMap_eq R (Polynomial R) (Localization.AtPrime p), RingHom.coe_comp,
        Set.image_comp, ← Ideal.map_span, ← Ideal.map_span]
      simp only [Ideal.span, (maximalIdeal R).span_generators, algebraMap_eq, q, ← eq,
        Localization.AtPrime.map_eq_maximalIdeal]
    simp only [← maximalIdeal_height_eq_ringKrullDim, ← IsLocalization.height_under p.primeCompl,
      IsLocalization.AtPrime.under_maximalIdeal _ p, ge_iff_le]
    apply le_trans _ (WithBot.coe_le_coe.mpr ht1)
    simp only [maximalIdeal_height_eq_ringKrullDim, ← reg, Nat.cast_le, ← this,
      ← Submodule.FG.generators_ncard fg']
    exact (Submodule.spanFinrank_span_le_ncard_of_finite (fg.image _)).trans (Set.ncard_image_le fg)
  · have lt : q < p := lt_of_le_of_ne qle (Ne.symm eq)
    have : (comap C p).IsMaximal := by simpa [max] using maximalIdeal.isMaximal R
    obtain ⟨y, _, hy⟩ := Polynomial.exists_monic_span_sup_map_eq R p this (by simpa [max])
    have peq : p = Ideal.span (((algebraMap R (Polynomial R)) '' (maximalIdeal R).generators) ∪ {y}) := by
      simp only [Ideal.span_union, ← Ideal.map_span, algebraMap_eq, sup_comm]
      nth_rw 1 [hy, max, ← (maximalIdeal R).span_generators]
    simp only [← Localization.AtPrime.map_eq_maximalIdeal, peq, Ideal.map_span]
    rw [← maximalIdeal_height_eq_ringKrullDim, ← IsLocalization.height_under p.primeCompl,
      IsLocalization.AtPrime.under_maximalIdeal _ p]
    apply le_trans _ (WithBot.coe_le_coe.mpr (Ideal.height_add_one_le_of_lt_of_isPrime lt))
    apply le_trans _ (WithBot.coe_le_coe.mpr (add_le_add_left ht 1))
    rw [WithBot.coe_add, maximalIdeal_height_eq_ringKrullDim, WithBot.coe_one, ← reg,
      ← Nat.cast_one, ← Nat.cast_add, Nat.cast_le]
    have fin := (fg.image (algebraMap R (Polynomial R))).union (Set.finite_singleton y)
    apply le_trans (Submodule.spanFinrank_span_le_ncard_of_finite (fin.image _))
    apply le_trans (Set.ncard_image_le fin) (le_trans (Set.ncard_union_le _ _) _)
    rw [Set.ncard_singleton, add_le_add_iff_right, ← Submodule.FG.generators_ncard fg']
    exact Set.ncard_image_le fg

attribute [-instance] OreLocalization.instSemiring OreLocalization.instCommSemiring
  AddMonoidAlgebra.semiring AddMonoidAlgebra.commSemiring

instance Polynomial.isRegularRing_of_isRegularRing [IsRegularRing R] : IsRegularRing (Polynomial R) := by
  apply isRegularRing_iff.mpr (fun p hp ↦ ?_)
  let q := p.comap C
  letI : CommRing (Localization.AtPrime q) := OreLocalization.instCommRing
  letI : CommSemiring (Localization.AtPrime q) := (inferInstance : CommRing (Localization.AtPrime q)).toCommSemiring
  letI : Semiring (Localization.AtPrime q) := (inferInstance : CommRing (Localization.AtPrime q)).toSemiring
  let S := (Localization.AtPrime q)[X]
  letI : CommRing S := AddMonoidAlgebra.commRing
  letI : CommSemiring S := (inferInstance : CommRing S).toCommSemiring
  letI : Semiring S := (inferInstance : CommRing S).toSemiring
  let pc := Submonoid.map Polynomial.C.toMonoidHom q.primeCompl
  let : Algebra (Polynomial R) S := algebra R (Localization.AtPrime q)
  have : IsLocalization pc S := Polynomial.isLocalization _ _
  let pS := p.map (algebraMap (Polynomial R) S)
  have disj : Disjoint (pc : Set (Polynomial R)) (p : Set (Polynomial R)) := by
    simpa [pc, q] using! Set.disjoint_image_left.mpr
      (Set.disjoint_compl_left_iff_subset.mpr (fun _ a ↦ a))
  have : pS.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint pc _ _ ‹_› disj
  letI : CommRing (Localization.AtPrime pS) := OreLocalization.instCommRing
  letI : CommSemiring (Localization.AtPrime pS) := (inferInstance : CommRing (Localization.AtPrime pS)).toCommSemiring
  letI : Semiring (Localization.AtPrime pS) := (inferInstance : CommRing (Localization.AtPrime pS)).toSemiring
  letI : CommRing (Localization.AtPrime p) := OreLocalization.instCommRing
  letI : CommSemiring (Localization.AtPrime p) := (inferInstance : CommRing (Localization.AtPrime p)).toCommSemiring
  letI : Semiring (Localization.AtPrime p) := (inferInstance : CommRing (Localization.AtPrime p)).toSemiring
  have : IsLocalization.AtPrime (Localization.AtPrime pS) p := by
    convert IsLocalization.isLocalization_isLocalization_atPrime_isLocalization pc
      (Localization.AtPrime pS) pS
    exact (IsLocalization.under_map_of_isPrime_disjoint pc _ ‹_› disj).symm
  have := isRegularRing_iff.mp ‹_› q
  have eq : comap C pS = maximalIdeal (Localization.AtPrime q) := by
    rw [← IsLocalization.map_under q.primeCompl _ (comap C pS),
      ← IsLocalization.map_under q.primeCompl _ (maximalIdeal (Localization.AtPrime q))]
    simp only [comap_comap, S, pS]
    rw [← Polynomial.algebraMap_eq (R := Localization.AtPrime q),
      ← IsScalarTower.algebraMap_eq R (Localization.AtPrime q) (Localization.AtPrime q)[X],
      IsScalarTower.algebraMap_eq R (Polynomial R) (Localization.AtPrime q)[X], ← comap_comap,
      ← Ideal.under_def (Polynomial R), IsLocalization.under_map_of_isPrime_disjoint pc _ ‹_› disj]
    simp [q, IsLocalization.AtPrime.under_maximalIdeal (Localization.AtPrime q) q]
  have := isRegularLocalRing_localization_atPrime_of_comap_eq_maximalIdeal _ pS eq
  let e : Localization.AtPrime pS ≃+* Localization.AtPrime p :=
    (IsLocalization.algEquiv p.primeCompl (Localization.AtPrime pS) (Localization.AtPrime p)).toRingEquiv
  exact IsRegularLocalRing.of_ringEquiv e

attribute [instance] OreLocalization.instSemiring OreLocalization.instCommSemiring
  AddMonoidAlgebra.semiring AddMonoidAlgebra.commSemiring

instance MvPolynomial.isRegularRing_of_isRegularRing [IsRegularRing R] {ι : Type*} [Finite ι] :
    IsRegularRing (MvPolynomial ι R) := by
  induction ι using Finite.induction_empty_option with
  | of_equiv e H => exact IsRegularRing.of_ringEquiv (renameEquiv _ e).toRingEquiv
  | h_empty => exact IsRegularRing.of_ringEquiv (isEmptyRingEquiv R _).symm
  | h_option IH =>
    exact IsRegularRing.of_ringEquiv (MvPolynomial.optionEquivLeft _ _).toRingEquiv.symm
