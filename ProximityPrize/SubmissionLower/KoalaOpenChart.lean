import ProximityPrize.SubmissionLower.KoalaLocalModel

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

namespace SplitCut.LocalModel
noncomputable section

open Polynomial HighCore82219Upper HighCore82219Upper_3
open HighCore82219Upper_4 (point modelValue origin)
open HighCore82219Upper_5_1 (valuePolynomial)
open HighCore82219Upper_3_1 (jetSeparant)
open HighCore82219Upper_3_1_2 (seedMap)
open HighCore82219Upper_3_3 (nodeAt wordAt)
open K1_14 (FX L Seeds Equation seedEmbedding)
open K1_14_6 (Biform)
open K1_14_6_1 (flatten separant markEval)
open P1 (K I node)
open StableFlow (CurveField curveMap)
open private HighCore82219Upper_3_1_2.eval_coefficient HighCore82219Upper_3_3_1.mark_biform
  HighCore82219Upper_3.seedBiform_image HighCore82219Upper_3_3.rootInJet_separant
  from ProximityPrize.SubmissionLower.HighCore82219UpperGeometry

abbrev openImage (J : Input) (B : ResidueLift J) (P : Ideal JetRing) : JetRing ⧸ P :=
  Ideal.Quotient.mk P (openFactor J B)

abbrev Chart (J : Input) (B : ResidueLift J) (P : Ideal JetRing) := Localization.Away (openImage J B P)

abbrev chartPoint (J : Input) (B : ResidueLift J) (P : Ideal JetRing) : JetRing →+* Chart J B P :=
  (algebraMap (JetRing ⧸ P) (Chart J B P)).comp (Ideal.Quotient.mk P)

abbrev chartBiform (J : Input) (B : ResidueLift J) (P : Ideal JetRing) : Biform →+* Chart J B P :=
  (chartPoint J B P).comp rootInJet.toRingHom

abbrev chartSeed (J : Input) (B : ResidueLift J) (P : Ideal JetRing) : SeedConstants →+* Chart J B P :=
  (chartBiform J B P).comp seedBiform

abbrev chartModel (J : Input) (B : ResidueLift J) (P : Ideal JetRing) : (Chart J B P)[X] :=
  model (chartBiform J B P) B (IsLocalization.Away.invSelf (openImage J B P))

theorem curve_map_nonzero (P : Ideal JetRing) [P.IsPrime] {q : JetRing} (hq : q ∉ P) :
    curveMap P q ≠ 0 := by
  intro h
  apply hq
  exact Ideal.Quotient.eq_zero_iff_mem.mp ((IsFractionRing.injective (JetRing ⧸ P) (CurveField P))
    (h.trans (map_zero _).symm))

theorem chart_domain (J : Input) (B : ResidueLift J) (P : Ideal JetRing) [P.IsPrime]
    (hP : openFactor J B ∉ P) : IsDomain (Chart J B P) := by
  have h : openImage J B P ≠ 0 := mt Ideal.Quotient.eq_zero_iff_mem.mp hP
  exact IsLocalization.isDomain_of_le_nonZeroDivisors (M := Submonoid.powers (openImage J B P)) _
    (powers_le_nonZeroDivisors_of_noZeroDivisors h)

theorem chartProduct {A : Type} [CommRing A] (φ : JetRing →+* A) (J : Input) (B : ResidueLift J) :
    (φ.comp rootInJet.toRingHom) (seedBiform B.denominator) *
      (φ.comp rootInJet.toRingHom) (separant (flatten J.f)) = φ (openFactor J B) := by
  change φ (C ((MvPolynomial.optionEquivLeft FX (Fin 2)) (seedBiform B.denominator))) *
    φ (rootInJet (separant (flatten J.f))) = φ (openFactor J B)
  rw [HighCore82219Upper_3.seedBiform_image, HighCore82219Upper_3_3.rootInJet_separant,
    openFactor, map_mul]
  rfl

theorem root_point {A : Type} [Field A] (φ : JetRing →+* A) :
    φ.comp rootInJet.toRingHom = point (seedMap φ) (φ ordinate) := by
  apply RingHom.ext
  intro f
  change φ (C (MvPolynomial.optionEquivLeft FX (Fin 2) f)) =
    (MvPolynomial.optionEquivLeft FX (Fin 2) f).eval₂ (seedMap φ) (φ ordinate)
  exact HighCore82219Upper_3_1_2.eval_coefficient φ _

theorem seed_lift_point {A : Type} [CommRing A] (φ : JetRing →+* A) :
    (φ.comp rootInJet.toRingHom).comp seedBiform = (seedMap φ).comp liftSeeds := by
  apply RingHom.ext
  intro s
  change φ (C ((MvPolynomial.optionEquivLeft FX (Fin 2)) (seedBiform s))) = _
  rw [HighCore82219Upper_3.seedBiform_image]
  rfl

theorem inv_image {A : Type} [Field A] {J : Input} {B : ResidueLift J}
    {P : Ideal JetRing} (ψ : Chart J B P →+* A) :
    ψ (IsLocalization.Away.invSelf (openImage J B P)) = (ψ (chartPoint J B P (openFactor J B)))⁻¹ := by
  have he : chartPoint J B P (openFactor J B) *
      IsLocalization.Away.invSelf (openImage J B P) = 1 := by
    change algebraMap (JetRing ⧸ P) (Chart J B P) (openImage J B P) *
      IsLocalization.Away.invSelf (openImage J B P) = 1
    exact IsLocalization.Away.mul_invSelf (openImage J B P)
  have hm : ψ (chartPoint J B P (openFactor J B)) * ψ (IsLocalization.Away.invSelf (openImage J B P)) = 1 := by
    rw [← map_mul, he, map_one]
  exact (inv_eq_of_mul_eq_one_right hm).symm

theorem model_specialization {A : Type} [Field A] {J : Input} {B : ResidueLift J}
    {P : Ideal JetRing} (ψ : Chart J B P →+* A) (φ : JetRing →+* A)
    (hψ : ψ.comp (chartPoint J B P) = φ) (ho : φ (openFactor J B) ≠ 0) :
    (chartModel J B P).map ψ = valuePolynomial (φ.comp rootInJet.toRingHom) J B := by
  have hg : ψ.comp (chartBiform J B P) = φ.comp rootInJet.toRingHom := by
    rw [← RingHom.comp_assoc, hψ]
  have hprod := chartProduct φ J B
  have hn := mul_ne_zero_iff.mp (hprod ▸ ho)
  rw [chartModel, model_map, hg, inv_image, show ψ (chartPoint J B P (openFactor J B)) =
    φ (openFactor J B) from RingHom.congr_fun hψ _ , ← hprod]
  exact model_of_inverse _ B hn.1 hn.2

/-- The curve chart injects into its function field and carries the exact
    reconstructed polynomial whose coefficients are constant under the flow. -/
theorem chart_to_curve (J : Input) (B : ResidueLift J) (P : Ideal JetRing) [P.IsPrime]
    (hP : openFactor J B ∉ P) (T : JetTaylor.Data (CurveField P))
    (hT : T.ι = seedMap (curveMap P)) :
    ∃ ψ : Chart J B P →+* CurveField P, Function.Injective ψ ∧
      ψ.comp (chartPoint J B P) = curveMap P ∧
      (chartModel J B P).map ψ = modelValue T.ι B (curveMap P ordinate) := by
  let A := JetRing ⧸ P
  let E := CurveField P
  let g := openImage J B P
  let f : A →+* E := algebraMap A E
  have hg : IsUnit (f g) := isUnit_iff_ne_zero.mpr (curve_map_nonzero _ hP)
  let ψ : Chart J B P →+* E := IsLocalization.Away.lift g hg
  have hψ (a : A) : ψ (algebraMap A (Chart J B P) a) = f a := IsLocalization.Away.lift_eq g hg a
  have hc : ψ.comp (chartPoint J B P) = curveMap P := by
    apply RingHom.ext
    intro a
    exact hψ (Ideal.Quotient.mk P a)
  have hi : Function.Injective ψ := by
    apply (IsLocalization.injective_iff_map_algebraMap_eq (Submonoid.powers g) ψ).mpr
    intro a b
    rw [hψ,hψ]
    constructor
    · intro hh
      have h := IsLocalization.injective (Chart J B P)
        (powers_le_nonZeroDivisors_of_noZeroDivisors (mt Ideal.Quotient.eq_zero_iff_mem.mp hP)) hh
      exact congrArg f h
    · exact fun h => congrArg (algebraMap A (Chart J B P)) ((IsFractionRing.injective A E) h)
  refine ⟨ψ, hi, hc, ?_⟩
  rw [model_specialization ψ _ hc (curve_map_nonzero P hP), root_point, ← hT]
  exact value_eq_taylor T _ J B

theorem chart_at_mark {J : Input} {B : ResidueLift J} {D : Factors J B}
    (C : CurveMarks J B D) (γ : K) (hγ : γ ∈ C.marks) :
    ∃ ψ : Chart J B C.prime →+* FX,
      ψ.comp (chartPoint J B C.prime) = (markPoint J γ).toRingHom ∧
      ∀ x : I, ψ ((chartModel J B C.prime).eval (chartSeed J B C.prime (MvPolynomial.C (algebraMap K L (node x))))) =
        seedEmbedding ((J.family.scalar γ).eval (node x)) := by
  let P := C.prime
  let A := JetRing ⧸ P
  let q := Ideal.Quotient.mk P
  let g := openImage J B P
  let φ := (markPoint J γ).toRingHom
  let f := Ideal.Quotient.lift P φ (fun a ha => RingHom.mem_ker.mp (C.liesOn γ hγ ha))
  have hγ' := C.sub hγ
  have hunit : IsUnit (f g) := isUnit_iff_ne_zero.mpr (HighCore82219Upper_3_3_1.proof J B γ hγ').1
  let ψ : Chart J B P →+* FX := IsLocalization.Away.lift g hunit
  have hψ (a : A) : ψ (algebraMap A (Chart J B P) a) = f a := IsLocalization.Away.lift_eq g hunit a
  have hc : ψ.comp (chartPoint J B P) = φ := by
    apply RingHom.ext
    intro a
    exact hψ (q a)
  refine ⟨ψ,hc,fun x => ?_⟩
  have hφ : φ.comp rootInJet.toRingHom = markEval (J.model.label γ) (J.family.scalar γ) := by
    apply RingHom.ext
    intro a
    exact HighCore82219Upper_3_3_1.mark_biform J γ a
  have hθ (s : SeedConstants) : ψ (chartSeed J B P s) = (φ.comp rootInJet.toRingHom) (seedBiform s) :=
    RingHom.congr_fun hc (rootInJet (seedBiform s))
  have hv : ψ (chartSeed J B P (MvPolynomial.C (algebraMap K L (node x)))) = seedEmbedding (node x) := by
    rw [hθ, hφ]
    change markEval _ _ (MvPolynomial.rename some (MvPolynomial.map constantAbscissa
      (MvPolynomial.C (algebraMap K L (node x))))) = _
    rw [MvPolynomial.map_C, MvPolynomial.rename_C]
    exact MvPolynomial.eval_C _
  change ψ ((_ : (Chart J B P)[X]).eval _) = _
  rw [← eval_map_apply, hv, model_specialization ψ φ hc (HighCore82219Upper_3_3_1.proof J B γ hγ').1, hφ]
  exact value_at_mark J B γ hγ' x

end
end SplitCut.LocalModel
