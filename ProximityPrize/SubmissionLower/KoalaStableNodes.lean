import ProximityPrize.SubmissionLower.KoalaStableFlow
import ProximityPrize.SubmissionLower.KoalaFreshRoot
import ProximityPrize.SubmissionLower.KoalaNodeTranslation
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.RingTheory.Polynomial.DegreeLT
import ArkLib.Data.Polynomial.ResultantDegree
import Mathlib.Tactic
import ProximityPrize.SubmissionLower.KoalaBoxDegree
import ArkLib.Data.MvPolynomial.WeightAtMost
import Mathlib.LinearAlgebra.Matrix.Rank
import ProximityPrize.SubmissionLower.KoalaJetTaylor
import ProximityPrize.SubmissionLower.KoalaRawBounds

-- merged module KoalaLocalModel
section Merged_KoalaLocalModel
set_option autoImplicit false
set_option maxHeartbeats 1900000
set_option backward.isDefEq.respectTransparency false

namespace SplitCut.LocalModel
noncomputable section

open Polynomial Finset HighCore82258Upper HighCore82258Upper_3
open HighCore82258Upper_4 (point modelValue crt blocks jet origin)
open HighCore82258Upper_5_1 (constantLift valuePolynomial eval_denominator cleared_value marked_value)
open HighCore82258Upper_3_1_2 (seedMap)
open HighCore82258Upper_3_1 (jetSeparant)
open K1_14 (FX L Seeds Equation seedEmbedding)
open K1_14_6 (Biform)
open K1_14_6_1 (flatten separant markEval)
open P1 (K I node)
open private HighCore82258Upper_3_1_2.eval_coefficient HighCore82258Upper_3_3_1.mark_biform
  HighCore82258Upper_2.factorial_ne_zero HighCore82258Upper_5_2.charFX
  from ProximityPrize.SubmissionLower.HighCore82258UpperGeometry

/-- The reconstructed polynomial on the open chart, with the only inverse
    supplied as the inverse of the product of residue and separant. -/
def model {A : Type} [CommRing A] (ev : Biform →+* A) {J : Input} (B : ResidueLift J) (u : A) : A[X] :=
  let a := ev (seedBiform B.denominator)
  let s := ev (separant (flatten J.f))
  C (s*u) * B.numerator.map (ev.comp seedBiform) +
    J.blockProduct.map (ev.comp constantLift) *
      ∑ r ∈ range (J.ell+1),
        C (ev (quotientNumerator J B r) * (s*u) * (a*u)^(2*r-1)) *
          (Polynomial.X - C (ev (MvPolynomial.C center)))^r

theorem model_map {A E : Type} [CommRing A] [CommRing E]
    (ev : Biform →+* A) (ψ : A →+* E) {J : Input} (B : ResidueLift J) (u : A) :
    (model ev B u).map ψ = model (ψ.comp ev) B (ψ u) := by
  simp only [model, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C,
    Polynomial.map_map, Polynomial.map_sum, Polynomial.map_pow, Polynomial.map_sub,
    Polynomial.map_X, map_mul, map_pow, RingHom.comp_apply, RingHom.comp_assoc]

theorem model_of_inverse {E : Type} [Field E] (ev : Biform →+* E) {J : Input} (B : ResidueLift J)
    (hD : ev (seedBiform B.denominator) ≠ 0) (hs : ev (separant (flatten J.f)) ≠ 0) :
    model ev B (ev (seedBiform B.denominator) * ev (separant (flatten J.f)))⁻¹ =
      valuePolynomial ev J B := by
  let a := ev (seedBiform B.denominator)
  let s := ev (separant (flatten J.f))
  have ha : s * (a*s)⁻¹ = a⁻¹ := by
    rw [mul_inv, mul_left_comm, mul_inv_cancel₀ (show s ≠ 0 from hs), mul_one]
  have he : a * (a*s)⁻¹ = s⁻¹ := by
    rw [mul_inv, ← mul_assoc, mul_inv_cancel₀ (show a ≠ 0 from hD), one_mul]
  let n := fun r => ev (quotientNumerator J B r)
  let Xc := (Polynomial.X : E[X]) - C (ev (MvPolynomial.C center))
  change C (s*(a*s)⁻¹) * B.numerator.map (ev.comp seedBiform) +
      J.blockProduct.map (ev.comp constantLift) *
        ∑ r ∈ range (J.ell+1), C (n r * (s*(a*s)⁻¹) * (a*(a*s)⁻¹)^(2*r-1)) * Xc^r =
      C a⁻¹ * B.numerator.map (ev.comp seedBiform) +
      J.blockProduct.map (ev.comp constantLift) *
        ∑ r ∈ range (J.ell+1), C (n r / ev (quotientDenominator J B r)) * Xc^r
  simp only [ha, he]
  simp only [eval_denominator, div_eq_mul_inv, mul_inv, mul_assoc, inv_pow] <;> rfl

theorem value_eq_taylor {E : Type} [Field E] (T : JetTaylor.Data E) (y : E)
    (J : Input) (B : ResidueLift J) :
    valuePolynomial (point T.ι y) J B = modelValue T.ι B y := by
  have hb : point T.ι y (seedBiform B.denominator) = T.ι (liftSeeds B.denominator) :=
    RingHom.congr_fun (JetTaylor.point_seed T y) _
  have hg : (point T.ι y).comp constantLift = (T.ι.comp liftSeeds).comp MvPolynomial.C := by
    apply RingHom.ext
    intro a
    change point T.ι y (MvPolynomial.C (constantAbscissa a)) =
      T.ι (MvPolynomial.map constantAbscissa (MvPolynomial.C a))
    rw [JetTaylor.point_C, MvPolynomial.map_C]
    rfl
  rw [valuePolynomial, modelValue, crt, blocks, hb, JetTaylor.point_seed, hg, JetTaylor.point_C]
  rfl

theorem value_at_mark (J : Input) (B : ResidueLift J) (γ : K) (hγ : γ ∈ J.marks) (x : I) :
    (valuePolynomial (markEval (J.model.label γ) (J.family.scalar γ)) J B).eval (seedEmbedding (node x)) =
      seedEmbedding ((J.family.scalar γ).eval (node x)) := by
  let ev := markEval (J.model.label γ) (J.family.scalar γ)
  have he := marked_value J B γ hγ
  have hd : ev (HighCore82258Upper_5_1.denominator J B) ≠ 0 := he.1
  have hb : ev (seedBiform B.denominator) ≠ 0 := by
    have h := hd
    rw [HighCore82258Upper_5_1.denominator, eval_denominator, mul_ne_zero_iff] at h
    exact h.1
  have hs : ev (separant (flatten J.f)) ≠ 0 := by
    rw [K1_14_6_1.eval_separant]
    exact (J.regular γ hγ).2.2
  have h := (cleared_value ev J B hb hs (node x)).symm.trans (he.2 (node x))
  apply mul_left_cancel₀ hd
  simpa only [show ev (MvPolynomial.C (seedEmbedding (node x))) = seedEmbedding (node x) from
    MvPolynomial.eval_C _] using h

end
end SplitCut.LocalModel

#print axioms SplitCut.LocalModel.model_map
#print axioms SplitCut.LocalModel.model_of_inverse
#print axioms SplitCut.LocalModel.value_at_mark
end Merged_KoalaLocalModel

-- merged module KoalaOpenChart
section Merged_KoalaOpenChart
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

namespace SplitCut.LocalModel
noncomputable section

open Polynomial HighCore82258Upper HighCore82258Upper_3
open HighCore82258Upper_4 (point modelValue origin)
open HighCore82258Upper_5_1 (valuePolynomial)
open HighCore82258Upper_3_1 (jetSeparant)
open HighCore82258Upper_3_1_2 (seedMap)
open HighCore82258Upper_3_3 (nodeAt wordAt)
open K1_14 (FX L Seeds Equation seedEmbedding)
open K1_14_6 (Biform)
open K1_14_6_1 (flatten separant markEval)
open P1 (K I node)
open StableFlow (CurveField curveMap)
open private HighCore82258Upper_3_1_2.eval_coefficient HighCore82258Upper_3_3_1.mark_biform
  HighCore82258Upper_3.seedBiform_image HighCore82258Upper_3_3.rootInJet_separant
  from ProximityPrize.SubmissionLower.HighCore82258UpperGeometry

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
  rw [HighCore82258Upper_3.seedBiform_image, HighCore82258Upper_3_3.rootInJet_separant,
    openFactor, map_mul]
  rfl

theorem root_point {A : Type} [Field A] (φ : JetRing →+* A) :
    φ.comp rootInJet.toRingHom = point (seedMap φ) (φ ordinate) := by
  apply RingHom.ext
  intro f
  change φ (C (MvPolynomial.optionEquivLeft FX (Fin 2) f)) =
    (MvPolynomial.optionEquivLeft FX (Fin 2) f).eval₂ (seedMap φ) (φ ordinate)
  exact HighCore82258Upper_3_1_2.eval_coefficient φ _

theorem seed_lift_point {A : Type} [CommRing A] (φ : JetRing →+* A) :
    (φ.comp rootInJet.toRingHom).comp seedBiform = (seedMap φ).comp liftSeeds := by
  apply RingHom.ext
  intro s
  change φ (C ((MvPolynomial.optionEquivLeft FX (Fin 2)) (seedBiform s))) = _
  rw [HighCore82258Upper_3.seedBiform_image]
  rfl

private theorem inv_image {A : Type} [Field A] {J : Input} {B : ResidueLift J}
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

private theorem model_specialization {A : Type} [Field A] {J : Input} {B : ResidueLift J}
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
  have hunit : IsUnit (f g) := isUnit_iff_ne_zero.mpr (HighCore82258Upper_3_3_1.proof J B γ hγ').1
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
    exact HighCore82258Upper_3_3_1.mark_biform J γ a
  have hθ (s : SeedConstants) : ψ (chartSeed J B P s) = (φ.comp rootInJet.toRingHom) (seedBiform s) :=
    RingHom.congr_fun hc (rootInJet (seedBiform s))
  have hv : ψ (chartSeed J B P (MvPolynomial.C (algebraMap K L (node x)))) = seedEmbedding (node x) := by
    rw [hθ, hφ]
    change markEval _ _ (MvPolynomial.rename some (MvPolynomial.map constantAbscissa
      (MvPolynomial.C (algebraMap K L (node x))))) = _
    rw [MvPolynomial.map_C, MvPolynomial.rename_C]
    exact MvPolynomial.eval_C _
  change ψ ((_ : (Chart J B P)[X]).eval _) = _
  rw [← eval_map_apply, hv, model_specialization ψ φ hc (HighCore82258Upper_3_3_1.proof J B γ hγ').1, hφ]
  exact value_at_mark J B γ hγ' x

end
end SplitCut.LocalModel

#print axioms SplitCut.LocalModel.chart_to_curve
#print axioms SplitCut.LocalModel.chart_at_mark
end Merged_KoalaOpenChart

-- merged module KoalaCutGeometry
section Merged_KoalaCutGeometry
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 1800000

namespace SplitCut

open Polynomial

/-- After compression, a polynomial relation over the differential constants can
    be evaluated at an independent abscissa. -/
theorem fresh_identity {C E : Type*} [Field C] [Field E] [Algebra C E]
    (p : ℕ) [CharP C p] (D : Derivation C E E) (x : E) (hx : D x = 1)
    (P : C[X]) (hp : P.natDegree < p) (hz : aeval x P = 0) : P = 0 := by
  by_cases h : P.natDegree = 0
  · rw [eq_C_of_natDegree_eq_zero h] at hz ⊢
    simpa using (algebraMap C E).injective (by simpa using hz :
      algebraMap C E (P.coeff 0) = algebraMap C E 0)
  · have hd : aeval x P.derivative = 0 := by
      have e := D.map_aeval P x
      simpa [hz, hx] using e.symm
    have lt := natDegree_derivative_lt h
    have hd0 := fresh_identity p D x hx P.derivative (lt.trans hp) hd
    have ce := congrArg (fun Q : C[X] => Q.coeff (P.natDegree - 1)) hd0
    have hh : P.natDegree - 1 + 1 = P.natDegree := by omega
    simp only [coeff_derivative, hh, coeff_natDegree, coeff_zero] at ce
    have hhC : ((P.natDegree-1 : ℕ) : C) + 1 = (P.natDegree : C) := by
      simpa only [Nat.cast_add, Nat.cast_one] using congrArg (Nat.cast (R := C)) hh
    rw [hhC] at ce
    have hn : (P.natDegree : C) ≠ 0 := by
      intro hn
      have hdv := (CharP.cast_eq_zero_iff C p P.natDegree).mp hn
      exact hp.not_ge (Nat.le_of_dvd (by omega) hdv)
    rcases mul_eq_zero.mp ce with h₁ | h₂
    · exact leadingCoeff_eq_zero.mp h₁
    · exact (hn h₂).elim
termination_by P.natDegree

/-- The opposite-axis terms in the seed-plane intersection are the row sums
    of the Sylvester determinant. -/
theorem seed_resultant {F : Type*} [Field F] (P Q : F[X][X])
    (a b c d : ℕ) (hp : P.natDegree ≤ a) (hq : Q.natDegree ≤ c)
    (hpc : ∀ i, (P.coeff i).natDegree ≤ b) (hqc : ∀ i, (Q.coeff i).natDegree ≤ d) :
    (P.resultant Q).natDegree ≤ a*d+c*b := by
  exact (natDegree_resultant_le_of_coeff_natDegree_le P Q P.natDegree Q.natDegree b d hpc hqc).trans
    (by simpa [add_comm] using Nat.add_le_add (Nat.mul_le_mul_right d hp) (Nat.mul_le_mul_right b hq))

/-- Polynomial nullspace compression. Rows may have degree `D`. With `m`
    independent rows it suffices to enforce all their coefficients below `p`.
    The vector returned has enough space left for substitution of the scalar
    polynomial, whose Y-powers consume at most `D` abscissa degrees. -/
theorem compress_rows {F : Type*} [Field F] (n m p D : ℕ) (hD : D < p)
    (hdim : m*p < n*(p-D)) (A : Fin m → Fin n → F[X])
    (hA : ∀ i j, (A i j).natDegree ≤ D) :
    ∃ w : Fin n → degreeLT F (p-D), w ≠ 0 ∧
      ∀ i, ∑ j, A i j * (w j : F[X]) = 0 := by
  classical
  have hs (w : Fin n → degreeLT F (p-D)) (i : Fin m) :
      (∑ j, A i j * (w j : F[X])) ∈ degreeLT F p := by
    apply Submodule.sum_mem
    intro j _
    by_cases hw : (w j : F[X]) = 0
    · simp [hw]
    by_cases ha : A i j = 0
    · simp [ha]
    apply mem_degreeLT.mpr
    apply (natDegree_lt_iff_degree_lt (mul_ne_zero ha hw)).mp
    have h := (natDegree_lt_iff_degree_lt hw).mpr
      (mem_degreeLT.mp (w j).property)
    have := natDegree_mul_le (p := A i j) (q := (w j : F[X]))
    have := hA i j
    omega
  let M : (Fin n → degreeLT F (p-D)) →ₗ[F] (Fin m → degreeLT F p) :=
    { toFun := fun w i => ⟨∑ j, A i j * (w j : F[X]), hs w i⟩
      map_add' := by
        intro w z
        funext i
        apply Subtype.ext
        simp [mul_add, Finset.sum_add_distrib]
      map_smul' := by
        intro c w
        funext i
        apply Subtype.ext
        simp [Finset.smul_sum] }
  have hd (a b : ℕ) : Module.finrank F (Fin a → degreeLT F b) = a*b := by
    simp [Module.finrank_pi_fintype, (degreeLTEquiv F b).finrank_eq]
  have hni : ¬ Function.Injective M := fun hi => hdim.not_ge
    (by simpa only [hd] using LinearMap.finrank_le_finrank_of_injective hi)
  rw [LinearMap.ker_eq_bot.symm] at hni
  obtain ⟨w, hw, hn⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hni
  refine ⟨w, hn, fun i => ?_⟩
  exact congrArg Subtype.val (congrFun (LinearMap.mem_ker.mp hw) i)

/-- The referee's compression guard yields strict surplus for the polynomial
    nullspace after accounting for the known independent multiples. -/
theorem compression_guard {n k p D m : ℕ} (hk : k ≤ n) (hD : D ≤ p)
    (hm : m ≤ n-k) (hg : n*D < k*p) : m*p < n*(p-D) := by
  calc
    m*p ≤ (n-k)*p := Nat.mul_le_mul_right p hm
    _ < n*(p-D) := by
      zify [hk, hD] at hg ⊢
      nlinarith

abbrev Profile := ℚ → ℚ → ℚ → ℚ → ℚ

/-- Nef abscissa of the Hirzebruch surface, velocity, and the two seed lines. -/
def ambient (h t u v : ℚ) : ℚ := (t+1)*(h+t+1)*(u+1)*(v+1)

def cut (a b c d : ℚ) (P : Profile) (h t u v : ℚ) : ℚ :=
  P h t u v - P (h-a) (t-b) (u-c) (v-d)

/-- The mixed multiplicity of a root equation, its tangent, and two successive
    Taylor sections in the four-graded Hilbert polynomial. -/
theorem mixed_cut (e v₀ v₁ a b c₀ c₁ x y z₀ z₁ h t u w : ℚ) :
    cut (x-2*y) y z₀ z₁
      (cut (a-2*b) b c₀ c₁ (cut (e-2) 1 v₀ v₁ (cut e 0 v₀ v₁ ambient))) h t u w =
      e*(c₀*z₁+c₁*z₀) +
      (v₀*c₁+v₁*c₀)*((2*e-2)*y+x) + (v₀*z₁+v₁*z₀)*((2*e-2)*b+a) +
      2*v₀*v₁*((a-2*b)*y+x*b) := by
  unfold cut ambient
  ring

/-- With fixed side sum, moving area from the shorter side to the longer side
    decreases the remaining lattice-point count. -/
theorem outward_product (L S d : ℕ) (h : S ≤ L) : (L+d)*(S-d) ≤ L*S := by
  by_cases hd : d ≤ S
  · zify [hd] at h ⊢
    nlinarith [mul_nonneg (sub_nonneg.mpr h) (Int.natCast_nonneg d),
      sq_nonneg (d : ℤ)]
  · simp [Nat.sub_eq_zero_of_le (by omega : S ≤ d)]

theorem balanced_product {u v l r : ℤ} (hs : u+v=l+r) (h₀ : l≤r) (h₁ : r≤l+1) :
    u*v ≤ l*r := by
  have hv : v = l+r-u := by omega
  subst v
  by_cases h : u ≤ l
  · nlinarith [mul_nonneg (sub_nonneg.mpr h) (sub_nonneg.mpr (h.trans h₀))]
  · have h' : r ≤ u := by omega
    nlinarith [mul_nonneg (sub_nonneg.mpr h') (sub_nonneg.mpr (h₀.trans h'))]

end SplitCut

#print axioms SplitCut.fresh_identity
#print axioms SplitCut.seed_resultant
#print axioms SplitCut.compress_rows
#print axioms SplitCut.compression_guard
#print axioms SplitCut.mixed_cut
#print axioms SplitCut.outward_product
#print axioms SplitCut.balanced_product
end Merged_KoalaCutGeometry

-- merged module KoalaCompression
section Merged_KoalaCompression
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace SplitCut.Compression

noncomputable section

open Polynomial Matrix MvPolynomial
open scoped BigOperators

variable {F : Type*} [Field F]

abbrev Rational (F : Type*) [Field F] := FractionRing F[X]

/-- A basis chosen from the physical evaluation rows preserves their degree bound.
    Solving the coefficient equations on the basis solves every row. -/
theorem compress_matrix {α ι : Type*} [Finite α] [Fintype ι]
    (A : Matrix α ι F[X]) (p D k : ℕ) (hk : k ≤ Fintype.card ι)
    (hA : ∀ i j, (A i j).natDegree ≤ D) (hguard : Fintype.card ι * D < k * p)
    (hker : k ≤ Module.finrank (Rational F)
      (LinearMap.ker (A.map (algebraMap F[X] (Rational F))).mulVecLin)) :
    ∃ w : ι → degreeLT F (p-D), w ≠ 0 ∧ ∀ i, ∑ j, A i j * (w j : F[X]) = 0 := by
  classical
  let E := Rational F
  let a : F[X] →+* E := algebraMap F[X] E
  let M : Matrix α ι E := A.map a
  let R := Submodule.span E (Set.range M.row)
  let m := Module.finrank E R
  let n := Fintype.card ι
  change k ≤ n at hk
  change n * D < k * p at hguard
  have hdim := M.mulVecLin.finrank_range_add_finrank_ker
  change M.rank + _ = _ at hdim
  rw [M.rank_eq_finrank_span_row, Module.finrank_pi_fintype] at hdim
  have hn : m + Module.finrank E (LinearMap.ker M.mulVecLin) = n := by
    simpa [m, n, R] using hdim
  have hm : m ≤ n-k := by
    change k ≤ Module.finrank E (LinearMap.ker M.mulVecLin) at hker
    omega
  have hD : D < p := by
    by_contra! h
    have h₁ := Nat.mul_le_mul_left n h
    have h₂ := Nat.mul_le_mul_right p hk
    omega
  obtain ⟨B, hmem, hspan, _⟩ := Submodule.exists_fun_fin_finrank_span_eq E (Set.range M.row)
  change Fin m → (ι → E) at B
  choose row hrow using hmem
  let j := Fintype.equivFin ι
  have hmargin := SplitCut.compression_guard hk hD.le hm hguard
  obtain ⟨v, hv, hvA⟩ := SplitCut.compress_rows n m p D hD hmargin
    (fun i l => A (row i) (j.symm l)) (fun _ _ => hA _ _)
  let w : ι → degreeLT F (p-D) := fun l => v (j l)
  have hw : w ≠ 0 := by
    intro h
    apply hv
    ext i : 1
    simpa [w] using congrFun h (j.symm i)
  refine ⟨w, hw, fun i => ?_⟩
  have hB (i : Fin m) : B i ⬝ᵥ (fun l => a (w l : F[X])) = 0 := by
    rw [← hrow i]
    have he : (∑ l : Fin n, A (row i) (j.symm l) * (v l : F[X])) =
        ∑ l : ι, A (row i) l * (w l : F[X]) := by
      rw [← j.sum_comp]
      simp [w]
    have hh := congrArg a ((he.symm.trans (hvA i)))
    simpa only [map_sum, map_mul, map_zero, M, Matrix.row, Matrix.map_apply, dotProduct] using hh
  let vE : ι → E := fun l => a (w l : F[X])
  have hbi : M.row i ⬝ᵥ vE = 0 := by
    have hi : M.row i ∈ Submodule.span E (Set.range B) := by
      rw [hspan]
      exact Submodule.subset_span ⟨i, rfl⟩
    refine Submodule.span_induction (p := fun x _ => x ⬝ᵥ vE = 0) ?_ ?_ ?_ ?_ hi
    · rintro _ ⟨b, rfl⟩
      exact hB b
    · exact zero_dotProduct _
    · intro x y _ _ hx hy
      simp [add_dotProduct, hx, hy]
    · intro c x _ hx
      simp [smul_dotProduct, hx]
  apply IsFractionRing.injective F[X] E
  simpa only [map_sum, map_mul, map_zero, M, Matrix.row, Matrix.map_apply, vE, dotProduct] using hbi

open BoxDegree

private theorem card_exps (a b c : ℕ) : Fintype.card (exps a b c) = (a+1)*(b+1)*(c+1) := by
  rw [Fintype.card_congr (slots a b c)]
  simp [Nat.mul_assoc]

def evalRow {α : Type*} (S : α → F[X]) (z : α → Fin 2 → F)
    (g : α) (m : Exp) : F[X] :=
  S g ^ m none * Polynomial.C ((z g 0)^m (some 0) * (z g 1)^m (some 1))

private theorem eval_monomial_row {α : Type*} (S : α → F[X]) (z : α → Fin 2 → F)
    (g : α) (m : Exp) (a : Rational F) :
    MvPolynomial.eval (fun i : Idx => i.elim (algebraMap F[X] (Rational F) (S g))
      (fun j => algebraMap F[X] (Rational F) (Polynomial.C (z g j)))) (monomial m a) =
      algebraMap F[X] (Rational F) (evalRow S z g m) * a := by
  rw [MvPolynomial.eval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _),
    Fintype.prod_option, Fin.prod_univ_two]
  simp only [Option.elim_none, Option.elim_some, evalRow, map_mul, map_pow]
  ring

/-- A nonzero relation over the rational function field supplies the independent
    seed multiples which pay for compression of all physical evaluation rows. -/
theorem compress_box {α : Type*} [Finite α] (S : α → F[X]) (z : α → Fin 2 → F)
    {f : MvPolynomial Idx (Rational F)} (hf : f ≠ 0) {e v w b d p : ℕ}
    (hfit : f ∈ space (Rational F) e v w)
    (hS : ∀ g, (S g).natDegree ≤ d)
    (hroot : ∀ g, MvPolynomial.eval (fun i : Idx => i.elim (algebraMap F[X] (Rational F) (S g))
      (fun j => algebraMap F[X] (Rational F) (Polynomial.C (z g j)))) f = 0)
    (hguard : Fintype.card (exps e (v+b) (w+b))*(e*d) < ((b+1)*(b+1))*p) :
    ∃ W : exps e (v+b) (w+b) → degreeLT F (p-e*d), W ≠ 0 ∧
      ∀ g, ∑ m : exps e (v+b) (w+b), evalRow S z g m * (W m : F[X]) = 0 := by
  classical
  let E := Rational F
  let u : F[X] →+* E := algebraMap F[X] E
  let ι := exps e (v+b) (w+b)
  let A : Matrix α ι F[X] := Matrix.of (fun g m => evalRow S z g m)
  let B := space E e (v+b) (w+b)
  let C := space E 0 b b
  let coords : (ι → E) ≃ₗ[E] B := (basisRestrictSupport E ι).equivFun.symm
  let mul : C →ₗ[E] B := ((LinearMap.mulLeft E f).domRestrict _).codRestrict _ (by
    intro g
    change f * g.val ∈ _
    simpa only [Nat.add_zero] using mul_box hfit g.property)
  have hm (x : ι → E) (g : α) : (A.map u).mulVecLin x g =
      MvPolynomial.eval (fun i : Idx => i.elim (u (S g)) (fun j => u (Polynomial.C (z g j))))
        ((coords x).val) := by
    change (∑ m : ι, u (evalRow S z g m) * x m) = _
    have hx : ((coords x).val) = ∑ m : ι, monomial m.val (x m) := by
      change ((basisRestrictSupport E ι).equivFun.symm x : B).val = _
      rw [Module.Basis.equivFun_symm_apply]
      simp [MvPolynomial.coe_basisRestrictSupport_apply, MvPolynomial.smul_monomial]
    rw [hx, map_sum]
    exact Finset.sum_congr rfl fun m _ => (eval_monomial_row S z g m.val (x m)).symm
  let L := coords.symm.toLinearMap.comp mul
  have hL (x : C) : L x ∈ LinearMap.ker (A.map u).mulVecLin := by
    rw [LinearMap.mem_ker]
    funext g
    rw [hm]
    change MvPolynomial.eval _ ((coords (coords.symm (mul x))).val) = 0
    rw [LinearEquiv.apply_symm_apply]
    change MvPolynomial.eval _ (f*x.val) = 0
    rw [map_mul, hroot g, zero_mul]
  have hi : Function.Injective (L.codRestrict _ hL) := by
    intro x y hxy
    have h := congrArg (fun a : LinearMap.ker (A.map u).mulVecLin => a.val) hxy
    have he : mul x = mul y := coords.symm.injective h
    apply Subtype.ext
    exact mul_left_cancel₀ hf (congrArg Subtype.val he)
  have hker := LinearMap.finrank_le_finrank_of_injective hi
  change Module.finrank E C ≤ _ at hker
  rw [size (F:=E) 0 b b, zero_add, one_mul] at hker
  refine compress_matrix A p (e*d) ((b+1)*(b+1)) ?_ ?_ hguard hker
  · change _ ≤ Fintype.card (exps e (v+b) (w+b))
    rw [card_exps]
    have h : b+1 ≤ (e+1)*(v+b+1) := by
      simpa only [one_mul] using Nat.mul_le_mul (by omega : 1 ≤ e+1) (by omega : b+1 ≤ v+b+1)
    exact Nat.mul_le_mul h
      (by omega : b+1 ≤ w+b+1)
  · intro i j
    have h := natDegree_mul_le (p := S i ^ j.val none)
      (q := Polynomial.C ((z i 0)^j.val (some 0) * (z i 1)^j.val (some 1)))
    rw [natDegree_C, add_zero] at h
    exact h.trans (natDegree_pow_le_of_le _ (hS i) |>.trans (Nat.mul_le_mul_right _ j.2.1))

/-- Simple uniform compression guard for the active 69.50 grade range. -/
theorem koala_guard {e v w d : ℕ} (he : e ≤ 21) (hv : v ≤ 445) (hw : w ≤ 445)
    (hd : d ≤ 133606) :
    Fintype.card (exps e (v+128) (w+128)) * (e*d) < (129*129)*2130706433 := by
  rw [card_exps]
  calc
    (e+1)*(v+128+1)*(w+128+1)*(e*d) ≤ 22*574*574*(21*133606) := by
      exact Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul (by omega) (by omega)) (by omega))
        (Nat.mul_le_mul he hd)
    _ < _ := by decide

end
end SplitCut.Compression

#print axioms SplitCut.Compression.compress_matrix
#print axioms SplitCut.Compression.compress_box
#print axioms SplitCut.Compression.koala_guard
end Merged_KoalaCompression

-- merged module KoalaCompressedEquation
section Merged_KoalaCompressedEquation
set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace SplitCut.Compression
noncomputable section

open BoxDegree
open scoped Polynomial

variable {F : Type*} [Field F]

abbrev SeedPoly (F : Type*) [CommRing F] := MvPolynomial (Fin 2) F
abbrev FreshEquation (F : Type*) [CommRing F] := Polynomial (Polynomial (SeedPoly F))

def pack {e v w : ℕ} (W : exps e v w → F[X]) : FreshEquation F :=
  ∑ m : exps e v w,
    (W m).map (Polynomial.C.comp MvPolynomial.C) *
      Polynomial.C (Polynomial.monomial (m.val none) (MvPolynomial.monomial m.val.some 1))

theorem pack_coeff {e v w : ℕ} (W : exps e v w → F[X]) (i j : ℕ) :
    ((pack W).coeff i).coeff j =
      ∑ m : exps e v w, if m.val none = j then MvPolynomial.monomial m.val.some ((W m).coeff i) else 0 := by
  classical
  rw [pack, Polynomial.finsetSum_coeff, Polynomial.finsetSum_coeff]
  apply Finset.sum_congr rfl
  intro m _
  rw [Polynomial.coeff_mul_C, Polynomial.coeff_map, RingHom.comp_apply, Polynomial.coeff_C_mul,
    Polynomial.coeff_monomial]
  by_cases h : m.val none = j
  · simp [h, MvPolynomial.C_mul_monomial]
  · simp [h, Ne.symm h]

theorem pack_recover {e v w : ℕ} (W : exps e v w → F[X]) (m : exps e v w) (i : ℕ) :
    (((pack W).coeff i).coeff (m.val none)).coeff m.val.some = (W m).coeff i := by
  classical
  rw [pack_coeff, MvPolynomial.coeff_sum]
  rw [Finset.sum_eq_single m]
  · simp [MvPolynomial.coeff_monomial]
  · intro n _ hn
    by_cases h : n.val none = m.val none
    · have hs : n.val.some ≠ m.val.some := by
        intro he
        apply hn
        apply Subtype.ext
        ext j
        cases j with
        | none => exact h
        | some k => exact DFunLike.congr_fun he k
      simp [h, MvPolynomial.coeff_monomial, hs, Ne.symm hs]
    · simp [h]
  · intro h
    exact (h (Finset.mem_univ m)).elim

theorem pack_ne_zero {e v w : ℕ} {W : exps e v w → F[X]} (hW : W ≠ 0) : pack W ≠ 0 := by
  intro h
  apply hW
  funext m
  apply Polynomial.ext
  intro i
  rw [← pack_recover W m, h]
  simp

theorem pack_x_bound {e v w b : ℕ} (W : exps e v w → F[X])
    (hW : ∀ m, (W m).natDegree ≤ b) : (pack W).natDegree ≤ b := by
  unfold pack
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro m _
  exact Polynomial.natDegree_mul_le.trans (by
    rw [Polynomial.natDegree_C, add_zero]
    exact Polynomial.natDegree_map_le.trans (hW m))

theorem pack_y_bound {e v w : ℕ} (W : exps e v w → F[X]) (i : ℕ) :
    ((pack W).coeff i).natDegree ≤ e := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro j hj
  rw [pack_coeff]
  apply Finset.sum_eq_zero
  intro m _
  simp [show m.val none ≠ j from ne_of_lt (m.property.1.trans_lt hj)]

theorem pack_seed_bound {e v w : ℕ} (W : exps e v w → F[X]) (i j : ℕ) (a : Fin 2) :
    (((pack W).coeff i).coeff j).degreeOf a ≤ (![v,w] : Fin 2 → ℕ) a := by
  classical
  rw [pack_coeff]
  refine (MvPolynomial.degreeOf_sum_le a _ _).trans (Finset.sup_le ?_)
  intro m _
  split_ifs
  · apply MvPolynomial.degreeOf_le_iff.mpr
    intro n hn
    obtain rfl := Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset hn)
    fin_cases a
    · exact m.property.2.1
    · exact m.property.2.2
  · simp

theorem pack_substitute {A : Type*} [CommRing A] (ι : F →+* A) (z : Fin 2 → A) (S : A[X])
    {e v w : ℕ} (W : exps e v w → F[X]) :
    StableNode.substitute S ((pack W).map (Polynomial.mapRingHom (MvPolynomial.eval₂Hom ι z))) =
      ∑ m : exps e v w, (W m).map ι *
        (S^m.val none * Polynomial.C (z 0^m.val (some 0) * z 1^m.val (some 1))) := by
  rw [pack, Polynomial.map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro m _
  rw [Polynomial.map_mul, Polynomial.map_C, map_mul]
  congr 1
  · rw [Polynomial.map_map]
    change ((W m).map _).eval₂
      (Polynomial.eval₂RingHom Polynomial.C S) (Polynomial.X : A[X]) = _
    rw [Polynomial.eval₂_map]
    rw [show ((Polynomial.eval₂RingHom Polynomial.C S).comp
      (((Polynomial.mapRingHom (MvPolynomial.eval₂Hom ι z))).comp
        (Polynomial.C.comp MvPolynomial.C))) = Polynomial.C.comp ι by
          apply RingHom.ext
          intro q
          simp [Polynomial.map_C]]
    rw [← Polynomial.eval₂_map, Polynomial.eval₂_C_X]
  · simp only [StableNode.substitute, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C,
      Polynomial.coe_mapRingHom]
    change ((Polynomial.monomial (m.val none) (MvPolynomial.monomial m.val.some 1)).map
        (MvPolynomial.eval₂Hom ι z)).eval₂ Polynomial.C S = _
    rw [Polynomial.map_monomial, Polynomial.eval₂_monomial, MvPolynomial.eval₂Hom_monomial,
      Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fin.prod_univ_two, map_one, one_mul]
    exact mul_comm _ _

theorem compressed_polynomial {α : Type*} [Finite α] (S : α → F[X]) (z : α → Fin 2 → F)
    {f : MvPolynomial Idx (Rational F)} (hf : f ≠ 0) {e v w b d p : ℕ}
    (hfit : f ∈ space (Rational F) e v w) (hS : ∀ g, (S g).natDegree ≤ d)
    (hroot : ∀ g, MvPolynomial.eval (fun i : Idx => i.elim (algebraMap F[X] (Rational F) (S g))
      (fun j => algebraMap F[X] (Rational F) (Polynomial.C (z g j)))) f = 0)
    (hguard : Fintype.card (exps e (v+b) (w+b))*(e*d) < ((b+1)*(b+1))*p)
    (hp : e*d < p) :
    ∃ G : FreshEquation F, G ≠ 0 ∧ G.natDegree + e*d < p ∧
      (∀ i, (G.coeff i).natDegree ≤ e) ∧
      (∀ i j, (((G.coeff i).coeff j).degreeOf 0 ≤ v+b) ∧ (((G.coeff i).coeff j).degreeOf 1 ≤ w+b)) ∧
      (∀ g, StableNode.substitute (S g)
        (G.map (Polynomial.mapRingHom (MvPolynomial.eval (z g)))) = 0) := by
  classical
  obtain ⟨W, hW, hWzero⟩ := compress_box S z hf hfit hS hroot hguard
  let U : exps e (v+b) (w+b) → F[X] := fun m => W m
  have hU : U ≠ 0 := by
    intro h
    apply hW
    funext m
    exact Subtype.ext (congrFun h m)
  have hdeg (m : exps e (v+b) (w+b)) : (U m).natDegree ≤ p-e*d-1 := by
    by_cases hz : U m = 0
    · simp [hz]
    · have h := (Polynomial.natDegree_lt_iff_degree_lt hz).mpr
        (Polynomial.mem_degreeLT.mp (W m).property)
      omega
  refine ⟨pack U, pack_ne_zero hU, ?_, pack_y_bound U, ?_, ?_⟩
  · have h := pack_x_bound U hdeg
    omega
  · intro i j
    exact ⟨pack_seed_bound U i j 0, pack_seed_bound U i j 1⟩
  · intro g
    rw [show MvPolynomial.eval (z g) = MvPolynomial.eval₂Hom (RingHom.id F) (z g) from rfl,
      pack_substitute]
    simp only [Polynomial.map_id]
    simpa only [evalRow, U, mul_comm] using hWzero g

end
end SplitCut.Compression

#print axioms SplitCut.Compression.compressed_polynomial
end Merged_KoalaCompressedEquation

-- merged module KoalaSeedBounds
section Merged_KoalaSeedBounds
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000

namespace SplitCut.Compression
noncomputable section

open Polynomial
open K1_14 (FX L Seeds Equation)
open HighCore82258Upper (SeedConstants liftSeeds center)

private def axisSpace (F : Type*) [Field F] (i : Fin 2) (d : ℕ) : Submodule F (SeedPoly F) :=
  MvPolynomial.restrictSupport F {m | m i ≤ d}

private theorem axis_mem {F : Type*} [Field F] {i : Fin 2} {d : ℕ} {g : SeedPoly F} :
    g ∈ axisSpace F i d ↔ g.degreeOf i ≤ d := by
  exact (MvPolynomial.degreeOf_le_iff (f := g) (n := i)).symm

variable {F R : Type*} [Field F] [CommRing R] [Algebra F R]

private def coeffSpace (M : Submodule F R) : Submodule F R[X] where
  carrier := {P | ∀ j, P.coeff j ∈ M}
  zero_mem' := fun j => by rw [coeff_zero]; exact M.zero_mem
  add_mem' h₁ h₂ := fun j => by rw [coeff_add]; exact M.add_mem (h₁ j) (h₂ j)
  smul_mem' a _ hp := fun j => by rw [coeff_smul]; exact M.smul_mem a (hp j)

private theorem eval_mem (M : Submodule F R) {P : R[X]} (h : P ∈ coeffSpace M) (x : F) :
    P.eval (algebraMap F R x) ∈ M := by
  rw [eval_eq_sum_range]
  apply M.sum_mem
  intro j _
  rw [← map_pow, mul_comm, ← Algebra.smul_def]
  exact M.smul_mem _ (h j)

private theorem taylor_mem (M : Submodule F R) {P : R[X]} (h : P ∈ coeffSpace M) (x : F) :
    taylor (algebraMap F R x) P ∈ coeffSpace M := by
  intro j
  rw [taylor_coeff]
  apply eval_mem M (x := x)
  intro k
  rw [hasseDeriv_coeff, ← map_natCast (algebraMap F R), ← Algebra.smul_def]
  exact M.smul_mem _ (h _)

/-- Translating both polynomial coordinates over the constant field does not
    spend any degree on either seed axis. -/
theorem translated_seed_bound (G : FreshEquation F) (x w : F) (i : Fin 2) (d : ℕ)
    (h : ∀ m n, ((G.coeff m).coeff n).degreeOf i ≤ d) (m n : ℕ) :
    (((StableNode.translate (MvPolynomial.C x) (MvPolynomial.C w) G).coeff m).coeff n).degreeOf i ≤ d := by
  let M : Submodule F (SeedPoly F) := axisSpace F i d
  let N : Submodule F (Polynomial (SeedPoly F)) := coeffSpace M
  have hs : G.map (taylorAlgHom (MvPolynomial.C w : SeedPoly F)).toRingHom ∈ coeffSpace N := by
    intro j
    rw [coeff_map]
    change taylor (algebraMap F (SeedPoly F) w) (G.coeff j) ∈ coeffSpace M
    exact taylor_mem M (fun k => axis_mem.mpr (h j k)) w
  have ht := taylor_mem N hs x
  apply axis_mem.mp
  exact ht m n

def centerEquation (G : FreshEquation L) : Equation :=
  G.eval₂ (mapRingHom liftSeeds) (Polynomial.C (MvPolynomial.C center))

theorem center_axis_bound (G : FreshEquation L) (i : Fin 2) (v : ℕ)
    (h : ∀ m n, ((G.coeff m).coeff n).degreeOf i ≤ v) (n : ℕ) :
    ((centerEquation G).coeff n).degreeOf i ≤ v := by
  let M := axisSpace FX i v
  let N := coeffSpace M
  let P := G.map (mapRingHom liftSeeds)
  have hP : P ∈ coeffSpace N := by
    intro j k
    apply axis_mem.mpr
    simp only [P, coeff_map, coe_mapRingHom, liftSeeds]
    rw [MvPolynomial.degreeOf_eq_sup]
    exact (Finset.sup_mono (MvPolynomial.support_map_subset _ _)).trans
      (by simpa only [MvPolynomial.degreeOf_eq_sup] using h j k)
  have he : centerEquation G = P.eval (algebraMap FX Equation center) := by
    rw [centerEquation, eval_map]
    rfl
  rw [he]
  exact axis_mem.mp (eval_mem N hP center n)

theorem center_y_bound (G : FreshEquation L) (e : ℕ) (h : ∀ i, (G.coeff i).natDegree ≤ e) :
    (centerEquation G).natDegree ≤ e := by
  rw [centerEquation, eval₂_eq_sum_range]
  apply natDegree_sum_le_of_forall_le
  intro i _
  refine natDegree_mul_le.trans (Nat.add_le_add ?_ ?_ |>.trans_eq (Nat.add_zero _))
  · exact natDegree_map_le.trans (h i)
  · exact (natDegree_pow_le_of_le _ (natDegree_C _).le).trans_eq (Nat.mul_zero _)

theorem center_eval {E : Type} [CommRing E] (ι : Seeds →+* E) (y : E) (G : FreshEquation L) :
    (centerEquation G).eval₂ ι y =
      (G.map (mapRingHom (ι.comp liftSeeds))).eval₂ (evalRingHom y) (ι (MvPolynomial.C center)) := by
  change eval₂RingHom ι y (G.eval₂ (mapRingHom liftSeeds) (C (MvPolynomial.C center))) = _
  rw [hom_eval₂, eval₂_map, coe_eval₂RingHom, eval₂_C]
  congr 1
  apply RingHom.ext
  intro P
  change (P.map liftSeeds).eval₂ ι y = (P.map (ι.comp liftSeeds)).eval y
  rw [eval₂_map, eval_map]

end
end SplitCut.Compression

#print axioms SplitCut.Compression.translated_seed_bound
#print axioms SplitCut.Compression.center_axis_bound
end Merged_KoalaSeedBounds

-- merged module KoalaCompressionMarks
section Merged_KoalaCompressionMarks
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

namespace SplitCut.Compression
noncomputable section

open Polynomial HighCore82258Upper HighCore82258Upper_3
open K1_14 (L FX Equation liftPoly atX graphEval atMark seedEmbedding)
open K1_14_6 (Biform rootPoint)
open K1_14_6_1 (flatten markEval)
open P1 (K p)
open private HighCore82258Upper_3_2.seed_at_mark HighCore82258Upper_3_3_1.mark_biform
  HighCore82258Upper_2.seed_at_mark from ProximityPrize.SubmissionLower.HighCore82258UpperGeometry

structure MarkCompression (J : Input) (v w : ℕ) where
  G : FreshEquation L
  width : G.natDegree + J.e*P1_7.degreeAt J.hi < p
  yBound : ∀ i, (G.coeff i).natDegree ≤ J.e
  axes : ∀ i j, ((G.coeff i).coeff j).degreeOf 0 ≤ v+128 ∧
    ((G.coeff i).coeff j).degreeOf 1 ≤ w+128
  i : ℕ
  j : ℕ
  nonzero : (G.coeff i).coeff j ≠ 0
  atMarks : ∀ γ ∈ J.marks, atMark (centerEquation G) (J.model.label γ) (J.family.scalar γ) = 0

namespace MarkCompression

abbrev witness {J : Input} {v w : ℕ} (M : MarkCompression J v w) : SeedConstants :=
  (M.G.coeff M.i).coeff M.j

def good {J : Input} {v w : ℕ} (M : MarkCompression J v w) : Finset K := by
  classical
  exact J.marks.filter fun γ => evalSeedConstants (J.model.label γ) M.witness ≠ 0

theorem mem_good {J : Input} {v w : ℕ} (M : MarkCompression J v w) {γ : K} :
    γ ∈ M.good ↔ γ ∈ J.marks ∧ evalSeedConstants (J.model.label γ) M.witness ≠ 0 := by
  simp [good]

theorem bad_bound {J : Input} {v w : ℕ} (M : MarkCompression J v w) (hv : v ≤ 445) :
    (J.marks \ M.good).card ≤ (p+1)*(v+w+256) := by
  classical
  let B := J.marks \ M.good
  let a : K → L := fun γ => algebraMap K L (J.model.label γ)
  have ha : Set.InjOn a (B : Set K) := fun x _ y _ h => sub_left_inj.mp ((algebraMap K L).injective h)
  have hb : ∀ t ∈ B.image a, MvPolynomial.eval ![t,t^p] M.witness = 0 := by
    intro t ht
    obtain ⟨γ,hγ,rfl⟩ := Finset.mem_image.mp ht
    by_contra h
    exact (Finset.mem_sdiff.mp hγ).2 ((mem_good M).mpr ⟨(Finset.mem_sdiff.mp hγ).1,h⟩)
  have he := K1_14.frobenius_coefficient_exception_count p (v+128) (w+128) (by decide)
    M.witness M.nonzero (M.axes _ _).1 (show v+128<p by change v+128 < 2130706433; omega)
    (M.axes _ _).2 (B.image a) hb
  rw [Finset.card_image_of_injOn ha] at he
  refine he.trans ?_
  calc
    v+128+p*(w+128) ≤ (p+1)*(v+128)+(p+1)*(w+128) := by
      exact Nat.add_le_add (Nat.le_mul_of_pos_left _ (by omega)) (Nat.mul_le_mul_right _ (by omega))
    _ = _ := by ring

end MarkCompression

private theorem center_at_mark (J : Input) (G : FreshEquation L) (γ : K)
    (h : StableNode.substitute (liftPoly (J.family.scalar γ))
      (G.map (mapRingHom (evalSeedConstants (J.model.label γ)))) = 0) :
    atMark (centerEquation G) (J.model.label γ) (J.family.scalar γ) = 0 := by
  let z := J.model.label γ
  let s := J.family.scalar γ
  have hh := congrArg (Polynomial.map constantAbscissa) h
  rw [FreshRoot.map_substitute, Polynomial.map_zero, Polynomial.map_map] at hh
  have hseed : (mapRingHom constantAbscissa).comp (mapRingHom (evalSeedConstants z)) =
      mapRingHom ((graphEval z).comp liftSeeds) := by
    rw [HighCore82258Upper_3_2.seed_at_mark]
    apply RingHom.ext
    intro P
    exact Polynomial.map_map _ _ _
  have hA : ((liftPoly s).map constantAbscissa).eval center = atX s := by
    rw [eval_map]
    change (liftPoly s).eval₂ ((algebraMap L[X] FX).comp Polynomial.C)
      ((algebraMap L[X] FX) Polynomial.X) = _
    rw [← hom_eval₂, eval₂_C_X]
    rfl
  change (centerEquation G).eval₂ (graphEval z) (atX s) = 0
  rw [center_eval, show graphEval z (MvPolynomial.C center) = center from MvPolynomial.eval_C _,
    ← hseed, ← hA, ← FreshRoot.substitute_eval]
  rw [hh, eval_zero]

theorem compress_marks (J : Input) (v w : ℕ) (he : J.e ≤ 21) (hv : v ≤ 445) (hw : w ≤ 445)
    (hhi : J.hi ≤ 2535)
    (haxis : ∀ i, (J.f.coeff i).degreeOf 0 ≤ v ∧ (J.f.coeff i).degreeOf 1 ≤ w) :
    Nonempty (MarkCompression J v w) := by
  classical
  let α := {γ // γ ∈ J.marks}
  let S : α → L[X] := fun γ => liftPoly (J.family.scalar γ.val)
  let z : α → Fin 2 → L := fun γ =>
    ![algebraMap K L (J.model.label γ.val), (algebraMap K L (J.model.label γ.val))^p]
  have hf : flatten J.f ≠ 0 := by
    intro h
    have hz := (MvPolynomial.optionEquivLeft FX (Fin 2)).symm.injective (h.trans (map_zero _).symm)
    have hh := J.sheets
    change 3 ≤ J.f.natDegree at hh
    rw [hz, Polynomial.natDegree_zero] at hh
    omega
  have hfit := SplitCut.Raw.root (f:=J.f) le_rfl haxis
  have hS (g : α) : (S g).natDegree ≤ P1_7.degreeAt J.hi :=
    natDegree_map_le.trans ((HighCore82258Upper.fixed_word J (Finset.Subset.refl _)).degree _ g.property)
  have hroot (g : α) : MvPolynomial.eval (fun i : Option (Fin 2) => i.elim
      (algebraMap L[X] FX (S g)) (fun j => algebraMap L[X] FX (Polynomial.C (z g j))))
        (flatten J.f) = 0 := by
    have heq : (fun i : Option (Fin 2) => i.elim
      (algebraMap L[X] FX (S g)) (fun j => algebraMap L[X] FX (Polynomial.C (z g j)))) =
        rootPoint (J.model.label g.val) (J.family.scalar g.val) := by
      funext i
      cases i with
      | none => rfl
      | some j => fin_cases j <;> simp [z, rootPoint, seedEmbedding]
    rw [heq]
    exact (K1_14_6_1.eval_flatten _ _ _).trans (J.regular g.val g.property).1
  have hd : P1_7.degreeAt J.hi ≤ 133606 := by unfold P1_7.degreeAt; omega
  have hp : J.e*P1_7.degreeAt J.hi < p := by
    exact (Nat.mul_le_mul he hd).trans_lt (by decide)
  obtain ⟨G,hGn,hGx,hGy,hGz,hGmarks⟩ := compressed_polynomial S z hf hfit hS hroot
    (koala_guard he hv hw hd) hp
  have hsome : ∃ i j, (G.coeff i).coeff j ≠ 0 := by
    by_contra! h
    apply hGn
    apply Polynomial.ext
    intro i
    apply Polynomial.ext
    intro j
    simp [h i j]
  obtain ⟨i,j,hij⟩ := hsome
  refine ⟨⟨G,hGx,hGy,hGz,i,j,hij,fun γ hγ => ?_⟩⟩
  exact center_at_mark J G γ (hGmarks ⟨γ,hγ⟩)

end
end SplitCut.Compression

#print axioms SplitCut.Compression.compress_marks
#print axioms SplitCut.Compression.MarkCompression.bad_bound
end Merged_KoalaCompressionMarks

set_option autoImplicit false
set_option maxHeartbeats 3500000
set_option maxRecDepth 8000
set_option backward.isDefEq.respectTransparency false

namespace SplitCut.Compression
noncomputable section

open Polynomial HighCore82258Upper HighCore82258Upper_3
open HighCore82258Upper_4 (point modelValue origin blocks)
open HighCore82258Upper_3_1_2 (seedMap)
open K1_14 (L FX Equation atMark seedEmbedding)
open K1_14_6 (Biform)
open K1_14_6_1 (flatten separant markEval)
open P1 (K I node p)
open StableFlow LocalModel
open private HighCore82258Upper_3_1_2.eval_coefficient HighCore82258Upper_3_2.mark_C
  HighCore82258Upper_3.seedBiform_image HighCore82258Upper_3_3_1.mark_biform
  HighCore82258Upper_3_3.rootInJet_flatten
  HighCore82258Upper_2.seed_at_mark HighCore82258Upper_2.factorial_ne_zero HighCore82258Upper_5_2.charFX
  from ProximityPrize.SubmissionLower.HighCore82258UpperGeometry

private theorem seed_fit {e v w : ℕ} (g : SeedConstants)
    (hv : g.degreeOf 0 ≤ v) (hw : g.degreeOf 1 ≤ w) :
    seedBiform g ∈ BoxDegree.space FX e v w := by
  have he : seedBiform g = flatten (C (liftSeeds g)) := by
    apply (MvPolynomial.optionEquivLeft FX (Fin 2)).injective
    rw [HighCore82258Upper_3.seedBiform_image]
    exact ((MvPolynomial.optionEquivLeft FX (Fin 2)).apply_symm_apply _).symm
  rw [he]
  apply SplitCut.Raw.root (by simp : (C (liftSeeds g)).natDegree ≤ e)
  intro i
  cases i with
  | zero =>
    rw [Polynomial.coeff_C_zero]
    have h (k : Fin 2) : (liftSeeds g).degreeOf k ≤ g.degreeOf k := by
      simp only [liftSeeds, MvPolynomial.degreeOf_eq_sup]
      exact Finset.sup_mono (MvPolynomial.support_map_subset _ _)
    exact ⟨(h 0).trans hv,(h 1).trans hw⟩
  | succ i => simp

private theorem mark_seed_projection {J : Input} {B : ResidueLift J} {P : Ideal JetRing}
    (γ : K) (ψ : Chart J B P →+* FX) (hψ : ψ.comp (chartPoint J B P) = (markPoint J γ).toRingHom) :
    ψ.comp (chartSeed J B P) = constantAbscissa.comp (evalSeedConstants (J.model.label γ)) := by
  apply RingHom.ext
  intro g
  change ψ (chartPoint J B P (rootInJet (seedBiform g))) = _
  calc
    _ = markPoint J γ (rootInJet (seedBiform g)) := RingHom.congr_fun hψ _
    _ = markEval (J.model.label γ) (J.family.scalar γ) (seedBiform g) :=
      HighCore82258Upper_3_3_1.mark_biform J γ _
    _ = _ := RingHom.congr_fun (HighCore82258Upper_2.seed_at_mark (J.model.label γ) (J.family.scalar γ)) g

private theorem center_zero_on_curve {J : Input} {B : ResidueLift J} {D : Factors J B}
    (C₀ : CurveMarks J B D) (G : FreshEquation L)
    (hs : ∀ q ∈ C₀.prime, action J.f q ∈ C₀.prime) (hG : C (centerEquation G) ∈ C₀.prime)
    (hw : G.natDegree + J.e*P1_7.degreeAt J.hi < p)
    (hY : ∀ i, (G.coeff i).natDegree ≤ J.e) :
    StableNode.substitute (chartModel J B C₀.prime) (G.map (mapRingHom (chartSeed J B C₀.prime))) = 0 := by
  let P := C₀.prime
  let _ : P.IsPrime := C₀.isPrime
  let E := CurveField P
  let φ := curveMap P
  let ev := φ.comp rootInJet.toRingHom
  let y := φ ordinate
  have hopen : φ (openFactor J B) ≠ 0 := curve_map_nonzero P C₀.regular
  have hnon : ev (seedBiform B.denominator) ≠ 0 ∧ ev (separant (flatten J.f)) ≠ 0 := by
    apply mul_ne_zero_iff.mp
    rwa [chartProduct φ]
  have hsep : HighCore82258Upper_3_1.jetSeparant J.f ∉ P := fun h =>
    C₀.regular (P.mul_mem_left _ h)
  obtain ⟨T, hT⟩ := differential_curve J.f P hsep hs
  have hpoint : ev = point T.ι y := by rw [hT]; exact root_point φ
  have zero (q : JetRing) (hq : q ∈ P) : φ q = 0 := by
    change algebraMap (JetRing ⧸ P) E (Ideal.Quotient.mk P q) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hq, map_zero]
  have hf : point T.ι y (flatten J.f) = 0 := by
    rw [← hpoint]
    change φ (rootInJet (flatten J.f)) = 0
    rw [HighCore82258Upper_3_3.rootInJet_flatten]
    have hprod : (C J.f : JetRing) = C D.proper * C (∏ j, D.flat j) :=
      (congrArg (fun q : Equation => (C q : JetRing)) D.product).trans (map_mul C _ _)
    rw [hprod]
    exact zero _ (P.mul_mem_right _ (C₀.onGraph (proper_mem_graph J B D)))
  have ha : T.ι (liftSeeds B.denominator) ≠ 0 := by
    change (T.ι.comp liftSeeds) B.denominator ≠ 0
    rw [← RingHom.congr_fun (JetTaylor.point_seed T y) B.denominator, ← hpoint]
    exact hnon.1
  have hsep' : point T.ι y (separant (flatten J.f)) ≠ 0 := by
    rw [← hpoint]
    exact hnon.2
  have hcut : point T.ι y (quotientNumerator J B (J.ell+1)) = 0 := by
    rw [← hpoint]
    exact zero _ C₀.onCutoff
  have hfac (r : ℕ) (hr : r ≤ J.ell+1) : (r.factorial : E) ≠ 0 := by
    have h := J.factorial_guard
    change 131071+J.hi+1 < p at h
    change r ≤ 131071 - J.w + 1 at hr
    have hh := HighCore82258Upper_2.factorial_ne_zero (show r < p by omega)
    simpa only [map_natCast, map_zero] using T.embed.injective.ne hh
  have hb : (blocks T.ι J).eval (origin T.ι) ≠ 0 := by
    rw [JetTaylor.eval_blocks T]
    have hb' : J.blockProduct ≠ 0 := mul_ne_zero J.chart.1.ne_zero J.chart.2.2.2.1.ne_zero
    exact (map_ne_zero_iff T.embed T.embed.injective).mpr
      ((map_ne_zero_iff (algebraMap L[X] FX) (IsFractionRing.injective L[X] FX)).mpr hb')
  let : CharP FX p := HighCore82258Upper_5_2.charFX
  let : CharP E p := charP_of_injective_ringHom T.embed.injective p
  let S := modelValue T.ι B y
  have hconst := JetTaylor.model_constant T J B y hf ha hsep' hfac hcut
  have hcenter := JetTaylor.model_center T J B y hf ha hsep' hb
  have hroot : (G.map (mapRingHom (T.ι.comp liftSeeds))).eval₂ (evalRingHom (S.eval (origin T.ι)))
      (origin T.ι) = 0 := by
    change (G.map (mapRingHom (T.ι.comp liftSeeds))).eval₂ (evalRingHom ((modelValue T.ι B y).eval (origin T.ι))) _ = _
    rw [hcenter]
    change (G.map (mapRingHom (T.ι.comp liftSeeds))).eval₂ (evalRingHom y) (T.ι (MvPolynomial.C center)) = 0
    rw [← center_eval, hT]
    change (centerEquation G).eval₂ (seedMap φ) (φ ordinate) = 0
    rw [← HighCore82258Upper_3_1_2.eval_coefficient φ]
    exact zero _ hG
  have hz := FreshRoot.root_at_fresh_variable p (T.ι.comp liftSeeds) T.δ (origin T.ι)
    G S T.center_one T.frozen hconst hY (HighCore82258Upper_4.model_width _ _ _ _) hw hroot
  obtain ⟨ψ, hψ, hp, hmodel⟩ := chart_to_curve J B P C₀.regular T hT
  have hseed : ψ.comp (chartSeed J B P) = T.ι.comp liftSeeds := by
    rw [chartSeed, chartBiform, ← RingHom.comp_assoc, ← RingHom.comp_assoc, hp,
      seed_lift_point, hT]
  have hmap : (mapRingHom ψ).comp (mapRingHom (chartSeed J B P)) =
      mapRingHom (T.ι.comp liftSeeds) := by
    apply RingHom.ext
    intro Q
    rw [RingHom.comp_apply, coe_mapRingHom, coe_mapRingHom, map_map, hseed, coe_mapRingHom]
  apply Polynomial.map_injective ψ hψ
  rw [FreshRoot.map_substitute, hmodel, map_map, hmap, Polynomial.map_zero]
  exact hz

theorem stable_node {J : Input} {v w : ℕ} (M : MarkCompression J v w)
    (B : ResidueLift J) (D : Factors J B) (C₀ : CurveMarks J B D) (hgood : C₀.marks ⊆ M.good)
    (hstable : ∀ q ∈ C₀.prime, action J.f q ∈ C₀.prime) (x : I)
    (hfailing : ∃ γ ∈ C₀.marks, (J.family.scalar γ).eval (node x) ≠ J.model.word x) :
    ∃ g : Biform, g ∈ BoxDegree.space FX J.e (v+128) (w+128) ∧ rootInJet g ∉ C₀.prime ∧
      ∀ γ ∈ C₀.marks, (J.family.scalar γ).eval (node x) = J.model.word x →
        markPoint J γ (rootInJet g) = 0 := by
  classical
  let P := C₀.prime
  let _ : P.IsPrime := C₀.isPrime
  by_cases hroot : Polynomial.C (centerEquation M.G) ∈ P
  · let A := Chart J B P
    let θ := chartSeed J B P
    let S := chartModel J B P
    let _ : IsDomain A := chart_domain J B P C₀.regular
    obtain ⟨γ,hγ,hfail⟩ := hfailing
    obtain ⟨ψ,hψ,hspec⟩ := chart_at_mark C₀ γ hγ
    have hgoodγ := (MarkCompression.mem_good M).mp (hgood hγ)
    have hseed := mark_seed_projection γ ψ hψ
    have hneq : ψ (θ M.witness) ≠ 0 := by
      change (ψ.comp θ) M.witness ≠ 0
      rw [hseed]
      have hinj : Function.Injective (constantAbscissa : L →+* FX) :=
        (IsFractionRing.injective L[X] FX).comp Polynomial.C_injective
      exact (map_ne_zero_iff constantAbscissa hinj).mpr hgoodγ.2
    have hGn : M.G.map (mapRingHom θ) ≠ 0 := by
      intro h
      have hz := congrArg (fun G : Polynomial A[X] => (G.coeff M.i).coeff M.j) h
      rw [coeff_map, Polynomial.coeff_zero] at hz
      change ((M.G.coeff M.i).map θ).coeff M.j = 0 at hz
      rw [coeff_map] at hz
      change θ M.witness = 0 at hz
      exact hneq (by rw [hz, map_zero])
    have hfail' : S.eval (θ (MvPolynomial.C (algebraMap K L (node x)))) ≠
        θ (MvPolynomial.C (algebraMap K L (J.model.word x))) := by
      intro h
      have hh := congrArg ψ h
      rw [hspec x] at hh
      change _ = (ψ.comp θ) (MvPolynomial.C (algebraMap K L (J.model.word x))) at hh
      rw [hseed] at hh
      apply hfail
      apply seedEmbedding.injective
      rw [RingHom.comp_apply, evalSeedConstants, MvPolynomial.eval_C] at hh
      exact hh
    have hz := center_zero_on_curve C₀ M.G hstable hroot M.width M.yBound
    obtain ⟨i,j,hn,hcuts⟩ := StableNode.translated_coefficient θ M.G S
      (MvPolynomial.C (algebraMap K L (node x))) (MvPolynomial.C (algebraMap K L (J.model.word x)))
      hGn hz hfail'
    let H := StableNode.translate (MvPolynomial.C (algebraMap K L (node x)))
      (MvPolynomial.C (algebraMap K L (J.model.word x))) M.G
    let g := (H.coeff i).coeff j
    refine ⟨seedBiform g, seed_fit g ?_ ?_, ?_, ?_⟩
    · exact translated_seed_bound M.G _ _ 0 _ (fun m n => (M.axes m n).1) i j
    · exact translated_seed_bound M.G _ _ 1 _ (fun m n => (M.axes m n).2) i j
    · intro hg
      apply hn
      change algebraMap (JetRing ⧸ P) A (Ideal.Quotient.mk P (rootInJet (seedBiform g))) = 0
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr hg, map_zero]
    · intro η hη hhit
      obtain ⟨ρ,hρ,hev⟩ := chart_at_mark C₀ η hη
      have hseed := mark_seed_projection η ρ hρ
      have h := hcuts ρ (by
        rw [hev x, hhit]
        change _ = (ρ.comp θ) (MvPolynomial.C (algebraMap K L (J.model.word x)))
        rw [hseed]
        simp only [RingHom.comp_apply, evalSeedConstants, MvPolynomial.eval_C]
        rfl)
      exact (RingHom.congr_fun hρ (rootInJet (seedBiform g))).symm.trans h
  · refine ⟨flatten (centerEquation M.G), SplitCut.Raw.root (center_y_bound _ _ M.yBound) ?_, ?_, ?_⟩
    · intro i
      exact ⟨center_axis_bound _ 0 _ (fun j k => (M.axes j k).1) i,
        center_axis_bound _ 1 _ (fun j k => (M.axes j k).2) i⟩
    · rw [HighCore82258Upper_3_3.rootInJet_flatten]
      exact hroot
    · intro γ hγ _
      rw [HighCore82258Upper_3_3.rootInJet_flatten]
      exact (HighCore82258Upper_3_2.mark_C J γ _).trans (M.atMarks γ (C₀.sub hγ))

theorem compress_good (J : Input) (v w : ℕ) (_he : 7 ≤ J.e) (he : J.e ≤ 21)
    (hv : v ≤ 445) (hw : w ≤ 445) (hhi : J.hi ≤ 2535)
    (haxis : ∀ i, (J.f.coeff i).degreeOf 0 ≤ v ∧ (J.f.coeff i).degreeOf 1 ≤ w) :
    ∃ U : Finset K, U ⊆ J.marks ∧ (J.marks \ U).card ≤ (p+1)*(v+w+256) ∧
      ∀ (B : ResidueLift J) (D : Factors J B) (C₀ : CurveMarks J B D), C₀.marks ⊆ U →
        (∀ q ∈ C₀.prime, action J.f q ∈ C₀.prime) → ∀ x : I,
        (∃ γ ∈ C₀.marks, (J.family.scalar γ).eval (node x) ≠ J.model.word x) →
        ∃ g : Biform, g ∈ BoxDegree.space FX J.e (v+128) (w+128) ∧ rootInJet g ∉ C₀.prime ∧
          ∀ γ ∈ C₀.marks, (J.family.scalar γ).eval (node x) = J.model.word x →
            markPoint J γ (rootInJet g) = 0 := by
  obtain ⟨M⟩ := compress_marks J v w he hv hw hhi haxis
  exact ⟨M.good, fun _ hγ => ((MarkCompression.mem_good M).mp hγ).1, M.bad_bound hv, stable_node M⟩

end
end SplitCut.Compression

#print axioms SplitCut.Compression.compress_good