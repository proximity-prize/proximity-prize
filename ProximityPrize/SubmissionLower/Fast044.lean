import ArkLib.Data.Finset.PairwiseIntersection
import Mathlib.Algebra.AffineMonoid.Basic
import Mathlib.Algebra.Order.Monoid.Prod
import Mathlib.Algebra.Polynomial.Basis
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.BoxIntegral.UnitPartition
import Mathlib.Analysis.Convex.Intrinsic
import Mathlib.Analysis.Convex.Measure
import Mathlib.Analysis.Convex.Visible
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Combinatorics.Nullstellensatz
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Data.Finsupp.Interval
import Mathlib.Data.Set.Card.Arithmetic
import Mathlib.Data.Sym.NatCard
import Mathlib.LinearAlgebra.TensorProduct.Free
import Mathlib.RingTheory.Finiteness.Descent
import Mathlib.RingTheory.Flat.Equalizer
import Mathlib.RingTheory.Ideal.IsPrincipalPowQuotient
import Mathlib.RingTheory.KrullDimension.LocalRing
import Mathlib.RingTheory.RingHom.Unramified
import Mathlib.RingTheory.Spectrum.Prime.Homeomorph
import Mathlib.Topology.Algebra.MvPolynomial
import ProximityPrize.SubmissionLower.Pack_K1Defs
import ProximityPrize.SubmissionLower.Fast023
import ProximityPrize.SubmissionLower.Fast029
import ProximityPrize.SubmissionLower.Fast042
import ProximityPrize.SubmissionLower.SoloK1_13_1_1ArithmeticLogic
set_option Elab.async false

section PackSource_K1_14_3_2_3Aux4
set_option autoImplicit true
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
set_option maxHeartbeats 1500000

namespace K1_14_3_2_3

noncomputable section

open K1_14_3 MvPolynomial

private theorem linear_cut_bound {k τ : Type} [Field k] [Finite τ]
    (φ : MvPolynomial τ k →ₐ[k] MvPolynomial (Fin 2) k) (hφ : Function.Surjective φ)
    (F G : MvPolynomial (Fin 2) k) (hF : F ≠ 0)
    (hcop : ∀ H, F ∣ G * H → F ∣ H)
    (f : MvPolynomial τ k) (hf : φ f = G) (hlinear : f.totalDegree ≤ 1)
    (N : ℕ) (hN : affineDegree ((Ideal.span {F}).comap φ) ≤ (N : ℚ)) :
    let L := Ideal.span ({F, G} : Set (MvPolynomial (Fin 2) k))
    Module.Finite k (MvPolynomial (Fin 2) k ⧸ L) ∧
      Module.finrank k (MvPolynomial (Fin 2) k ⧸ L) ≤ N := by
  let A := (Ideal.span {F}).comap φ
  let L := Ideal.span ({F, G} : Set (MvPolynomial (Fin 2) k))
  change Module.Finite k (MvPolynomial (Fin 2) k ⧸ L) ∧ _
  by_cases htop : Ideal.span {F} = ⊤
  · have hL : L = ⊤ := by simp [L, Ideal.span_insert, htop]
    let : Subsingleton (MvPolynomial (Fin 2) k ⧸ L) := Ideal.Quotient.subsingleton_iff.mpr hL
    exact ⟨inferInstance, by rw [Module.finrank_eq_zero_of_subsingleton]; exact Nat.zero_le _⟩
  have hdim : (affineHilbertPolynomial A).natDegree = 1 := by
    rw [show A = (Ideal.span {F}).comap φ from rfl,
      natDegree_affineHilbertPolynomial_comap_of_surjective φ hφ]
    have h := natDegree_affineHilbertPolynomial_span_singleton_add_one hF htop
    simp only [Nat.card_eq_fintype_card, Fintype.card_fin] at h
    omega
  have hreg : IsLeftRegular (Ideal.Quotient.mk A f) := by
    intro x z hxz
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective z
    change Ideal.Quotient.mk A f * Ideal.Quotient.mk A x =
      Ideal.Quotient.mk A f * Ideal.Quotient.mk A z at hxz
    rw [← map_mul, ← map_mul, Ideal.Quotient.eq] at hxz
    apply Ideal.Quotient.eq.mpr
    change φ (x - z) ∈ Ideal.span {F}
    rw [Ideal.mem_span_singleton]
    apply hcop
    have hxz' : φ (f * x - f * z) ∈ Ideal.span {F} := hxz
    rw [Ideal.mem_span_singleton, ← mul_sub, map_mul, hf] at hxz'
    exact hxz'
  have hmap : (A ⊔ Ideal.span {f}).map φ = L := by
    rw [Ideal.map_sup, show A = (Ideal.span {F}).comap φ from rfl,
      Ideal.map_comap_of_surjective φ hφ, Ideal.map_span, Set.image_singleton, hf]
    exact (Ideal.span_insert F {G}).symm
  have hcomap : L.comap φ = A ⊔ Ideal.span {f} := by
    rw [← hmap, Ideal.comap_map_of_surjective φ hφ, sup_eq_left]
    exact (Ideal.comap_mono bot_le).trans le_sup_left
  obtain ⟨hD, hC⟩ := principalCut_natDegree_affineHilbertPolynomial_le_and_coeff_le hreg hlinear
  rw [hdim, Nat.sub_self] at hD hC
  have hzero : (affineHilbertPolynomial (L.comap φ)).natDegree = 0 :=
    hcomap ▸ Nat.eq_zero_of_le_zero hD
  have hzero' : (affineHilbertPolynomial L).natDegree = 0 := by
    rw [← natDegree_affineHilbertPolynomial_comap_of_surjective φ hφ]
    exact hzero
  let : Module.Finite k (MvPolynomial τ k ⧸ L.comap φ) :=
    moduleFinite_of_natDegree_affineHilbertPolynomial_eq_zero hzero
  let : Module.Finite k (MvPolynomial (Fin 2) k ⧸ L) :=
    moduleFinite_of_natDegree_affineHilbertPolynomial_eq_zero hzero'
  let g := Ideal.quotientMapₐ L φ (le_rfl : L.comap φ ≤ L.comap φ)
  have hg : Function.Bijective g :=
    ⟨Ideal.quotientMap_injective, Ideal.quotientMap_surjective (H := le_rfl) hφ⟩
  have hlen := (AlgEquiv.ofBijective g hg).toLinearEquiv.finrank_eq
  have hlead : affineDegree A = (affineHilbertPolynomial A).leadingCoeff := by
    simp [affineDegree, hdim]
  refine ⟨inferInstance, ?_⟩
  rw [← hlen, ← Nat.cast_le (α := ℚ), ← affineDegree_eq_finrank,
    affineDegree_of_natDegree_eq_zero hzero, hcomap]
  exact (by simpa using hC : _ ≤ (affineHilbertPolynomial A).leadingCoeff).trans (hlead ▸ hN)

private theorem proper_cancel {k : Type} [Field k] (F G : MvPolynomial (Fin 2) k)
    (hF : F ≠ 0) (h : ∀ D, Irreducible D → D ∣ F → ¬ D ∣ G) :
    ∀ H, F ∣ G * H → F ∣ H := by
  let : UniqueFactorizationMonoid k := PrincipalIdealRing.to_uniqueFactorizationMonoid
  let : UniqueFactorizationMonoid (MvPolynomial (Fin 2) k) :=
    MvPolynomial.uniqueFactorizationMonoid (Fin 2)
  intro H hH
  exact UniqueFactorizationMonoid.dvd_of_dvd_mul_right_of_no_prime_factors hF
    (fun hDF hDG hD => h _ (UniqueFactorizationMonoid.irreducible_iff_prime.mpr hD) hDF hDG) hH

private theorem mem_capped {F : Plane} {B J : ℕ}
    (hB : F.totalDegree ≤ B) (hJ : F.degreeOf 1 ≤ J) :
    F ∈ restrictCappedDegree (Fin 2) SectionField 1 B J := by
  rw [mem_restrictCappedDegree]
  exact fun _ he => ⟨(le_totalDegree he).trans hB, (le_degreeOf_of_mem_support 1 he).trans hJ⟩

/-- The capped affine plane bound includes the saving from the common point at infinity. -/
theorem capped_bound (F G : Plane) (B J B' J' : ℕ) (hB' : 0 < B') (hJ' : 0 < J')
    (hp : PlaneProper F G) (hF : PlaneCaps .seed B J 0 F) (hG : PlaneCaps .seed B' J' 0 G) :
    Module.Finite SectionField (PlaneQuotient F G) ∧
      Module.finrank SectionField (PlaneQuotient F G) ≤ B * J' + J * (B' - J') := by
  let φ := monomialMap SectionField (cappedDegreeExponents (Fin 2) 1 B' J')
  have hf := mem_capped hF.1 hF.2
  have hg := mem_capped hG.1 hG.2
  exact linear_cut_bound φ (monomialMap_cappedDegreeExponents_surjective hB' hJ') F G
    hp.left_ne (proper_cancel F G hp.left_ne hp.no_common) (monomialLift G hg)
    (monomialMap_monomialLift G hg) (totalDegree_monomialLift_le_one G hg) _
    (affineDegree_comap_cappedDegree_span_singleton_le hB' hJ' hp.left_ne hf)

/-- Ordinary total degree is the diagonal of the capped filtration. -/
theorem total_bound (F G : Plane) (U U' : ℕ) (hU' : 0 < U')
    (hp : PlaneProper F G) (hF : PlaneCaps .jets 0 0 U F) (hG : PlaneCaps .jets 0 0 U' G) :
    Module.Finite SectionField (PlaneQuotient F G) ∧
      Module.finrank SectionField (PlaneQuotient F G) ≤ U * U' := by
  simpa only [Nat.sub_self, mul_zero, add_zero] using
    capped_bound F G U U U' U' hU' hU' hp
      ⟨hF, (degreeOf_le_totalDegree F 1).trans hF⟩
      ⟨hG, (degreeOf_le_totalDegree G 1).trans hG⟩

private abbrev swapToOption := MvPolynomial.renameEquiv SectionField (finSuccEquiv 1)

private theorem mem_box {F : Plane} {U D : ℕ} (hF : PlaneCaps .ordinate 0 D U F) :
    swapToOption F ∈ restrictBidegree (Fin 1) SectionField U D := by
  have h0 : (swapToOption F).degreeOf none ≤ U := by
    rw [renameEquiv_apply, ← (show finSuccEquiv 1 0 = none from rfl),
      degreeOf_rename_of_injective (finSuccEquiv 1).injective]
    exact hF.1
  have h1 : (swapToOption F).degreeOf (some 0) ≤ D := by
    have h := finSuccEquiv_succ (0 : Fin 1)
    change finSuccEquiv 1 1 = some 0 at h
    rw [renameEquiv_apply, ← h, degreeOf_rename_of_injective (finSuccEquiv 1).injective]
    exact hF.2
  rw [mem_restrictBidegree]
  intro m hm
  refine ⟨(le_degreeOf_of_mem_support _ hm).trans h0, ?_⟩
  rw [Finsupp.degree_eq_sum, Fin.sum_univ_one, Finsupp.some_apply]
  exact (le_degreeOf_of_mem_support _ hm).trans h1

/-- The rectangular filtration measures the two product-line intersection bounds. -/
theorem box_bound (F G : Plane) (U D U' D' : ℕ) (hU' : 0 < U') (hD' : 0 < D')
    (hp : PlaneProper F G) (hF : PlaneCaps .ordinate 0 D U F)
    (hG : PlaneCaps .ordinate 0 D' U' G) :
    Module.Finite SectionField (PlaneQuotient F G) ∧
      Module.finrank SectionField (PlaneQuotient F G) ≤ U * D' + U' * D := by
  let b := bidegreeMap (Fin 1) SectionField U' D'
  let φ := swapToOption.symm.toAlgHom.comp b
  have hφ : Function.Surjective φ := swapToOption.symm.surjective.comp (bidegreeMap_surjective hU' hD')
  let g := bidegreeLift (swapToOption G) (mem_box hG)
  have hg : φ g = G := by
    change swapToOption.symm (b g) = G
    rw [show b g = swapToOption G from bidegreeMap_bidegreeLift _ _, AlgEquiv.symm_apply_apply]
  have hcomap : (Ideal.span {F}).comap φ = (Ideal.span {swapToOption F}).comap b := by
    ext x
    change (swapToOption.symm (b x) ∈ Ideal.span {F}) ↔
      (b x ∈ Ideal.span {swapToOption F})
    rw [Ideal.mem_span_singleton, Ideal.mem_span_singleton]
    constructor
    · intro h
      simpa only [AlgEquiv.apply_symm_apply] using map_dvd swapToOption h
    · intro h
      simpa only [AlgEquiv.symm_apply_apply] using map_dvd swapToOption.symm h
  apply linear_cut_bound φ hφ F G hp.left_ne (proper_cancel F G hp.left_ne hp.no_common)
    g hg (totalDegree_bidegreeLift_le_one _ _) _
  rw [hcomap]
  have hn := affineDegree_comap_bidegreeMap_span_singleton_le hU' hD'
    ((map_ne_zero_iff swapToOption swapToOption.injective).mpr hp.left_ne) (mem_box hF)
  simpa [Nat.card_eq_fintype_card, b, Nat.mul_comm D U'] using hn

end
end K1_14_3_2_3
end PackSource_K1_14_3_2_3Aux4
