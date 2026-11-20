import Mathlib.RingTheory.Regular.Flat
import ProximityPrize.SubmissionLower.Pack_K1Defs
import ProximityPrize.SubmissionLower.Fast017
import ProximityPrize.SubmissionLower.Fast018
import ProximityPrize.SubmissionLower.Fast019
set_option Elab.async false

section PackSource_K1_13_7_1Geometry
set_option autoImplicit true
namespace K1_13_7_1
noncomputable section
open Polynomial MvPolynomial K1_13 K1_13_6
open RingTheory.Sequence
open scoped Pointwise

theorem genericCoeffs_injective : Function.Injective genericCoeffs :=
  (algebraMap GenericField GeoField).injective.comp (IsFractionRing.injective Geom[X] GenericField)

theorem toGeneric_injective : Function.Injective toGeneric :=
  MvPolynomial.map_injective _ genericCoeffs_injective

private theorem mem_smul_top_iff_dvd {R : Type*} [CommRing R] (f x : R) :
    x ∈ f • (⊤ : Submodule R R) ↔ f ∣ x := by
  simp only [Submodule.mem_smul_pointwise_iff_exists, Submodule.mem_top, true_and, smul_eq_mul]
  exact exists_congr fun _ => eq_comm

attribute [local instance] MvPolynomial.algebraMvPolynomial in
/-- Properness survives the generic coefficient extension by flatness.
    Irreducibility of the original factor need not survive that extension. -/
theorem proper_generic (f g : Row 4) (hf : Irreducible f) (hg : ¬ f ∣ g) :
    IsRelPrime (toGeneric f) (toGeneric g) := by
  have hp : Prime f := UniqueFactorizationMonoid.irreducible_iff_prime.mp hf
  have hreg : IsWeaklyRegular (Row 4) [f, g] := by
    rw [isWeaklyRegular_cons_iff, isWeaklyRegular_singleton_iff]
    refine ⟨mul_right_injective₀ hp.ne_zero, ?_⟩
    apply (isSMulRegular_quotient_iff_mem_of_smul_mem _ _).mpr
    intro x hx
    exact (mem_smul_top_iff_dvd f x).mpr
      ((hp.dvd_mul.mp ((mem_smul_top_iff_dvd f (g * x)).mp hx)).resolve_left hg)
  let _ : Algebra Geom[X] GeoField := genericCoeffs.toAlgebra
  let _ : Module.IsTorsionFree Geom[X] GeoField :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr genericCoeffs_injective
  have hflat : Module.Flat (Row 4) GeoJets :=
    Module.Flat.of_linearEquiv (Algebra.IsPushout.equiv Geom[X] (Row 4) GeoField GeoJets).symm.toLinearEquiv
  have h := hreg.of_flat (S := GeoJets)
  change IsWeaklyRegular GeoJets [toGeneric f, toGeneric g] at h
  rw [isWeaklyRegular_cons_iff, isWeaklyRegular_singleton_iff] at h
  rintro a ⟨b, hb⟩ ⟨c, hc⟩
  have hzero : toGeneric f ≠ 0 := fun hz => hp.ne_zero (toGeneric_injective (hz.trans (map_zero _).symm))
  have hprod : toGeneric g * b = toGeneric f * c := by rw [hc, hb]; ring
  have hdiv : toGeneric f ∣ b := (mem_smul_top_iff_dvd _ _).mp
    (mem_of_isSMulRegular_quotient_of_smul_mem h.2
      ((mem_smul_top_iff_dvd _ _).mpr ⟨c, hprod⟩))
  obtain ⟨q, hq⟩ := hdiv
  have hb0 : b ≠ 0 := right_ne_zero_of_mul (hb ▸ hzero)
  have hu : a * q = 1 := mul_left_cancel₀ hb0 (by
    calc
      b * (a * q) = (a * b) * q := by ring
      _ = b := by rw [← hb, ← hq]
      _ = b * 1 := (mul_one _).symm)
  exact ⟨⟨a, q, hu, by rw [mul_comm, hu]⟩, rfl⟩

end
end K1_13_7_1
end PackSource_K1_13_7_1Geometry

section PackSource_K1_13_6_1_4Defs
set_option autoImplicit true
namespace K1_13_6_1_4

noncomputable section

open K1_13 K1_13_6 K1_13_6_1 K1_13_7_1
open scoped BigOperators

/-- The chamber boxes with positive top cap contain the coordinate simplex. -/
def FullChamber (a : Shape) : Prop := Chamber a ∧ 0 < a.t

abbrev PairSectionIndex (a h : Shape) := SectionIndex a ⊕ SectionIndex h
abbrev PairSectionField (a h : Shape) :=
  FractionRing (MvPolynomial (PairSectionIndex a h) GeoField)

/-- A generic section with its own independent block of coefficients. -/
def sectionWith {σ : Type*} (a : Shape) (ι : SectionIndex a → σ) :
    MvPolynomial (Fin 4) (FractionRing (MvPolynomial σ GeoField)) :=
  ∑ m ∈ boxMonomials a,
    MvPolynomial.C (algebraMap (MvPolynomial σ GeoField)
      (FractionRing (MvPolynomial σ GeoField)) (MvPolynomial.X (ι m))) *
      ∏ i : Fin 4, MvPolynomial.X i ^ (m i).val

/-- Length of the affine intersection with independent generic sections.
The two shape arguments specify the actual monomial systems. -/
def surfaceDegree (surface : Ideal GeoJets) (a h : Shape) : ℕ :=
  let F := PairSectionField a h
  let I := surface.map (MvPolynomial.map (algebraMap GeoField F)) ⊔
    Ideal.span {sectionWith a (Sum.inl : SectionIndex a → PairSectionIndex a h),
      sectionWith h (Sum.inr : SectionIndex h → PairSectionIndex a h)}
  Module.finrank F (MvPolynomial (Fin 4) F ⧸ I)

abbrev pairIdeal (F G : GeoJets) : Ideal GeoJets := Ideal.span {F, G}

end
end K1_13_6_1_4
end PackSource_K1_13_6_1_4Defs
