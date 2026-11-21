import ProximityPrize.SubmissionLower.KoalaStableFlow
import ProximityPrize.SubmissionLower.KoalaFreshRoot
import ProximityPrize.SubmissionLower.KoalaNodeTranslation

set_option autoImplicit false
set_option maxHeartbeats 1900000
set_option backward.isDefEq.respectTransparency false

namespace SplitCut.LocalModel
noncomputable section

open Polynomial Finset HighCore82229Upper HighCore82229Upper_3
open HighCore82229Upper_4 (point modelValue crt blocks jet origin)
open HighCore82229Upper_5_1 (constantLift valuePolynomial eval_denominator cleared_value marked_value)
open HighCore82229Upper_3_1_2 (seedMap)
open HighCore82229Upper_3_1 (jetSeparant)
open K1_14 (FX L Seeds Equation seedEmbedding)
open K1_14_6 (Biform)
open K1_14_6_1 (flatten separant markEval)
open P1 (K I node)
open private HighCore82229Upper_3_1_2.eval_coefficient HighCore82229Upper_3_3_1.mark_biform
  HighCore82229Upper_2.factorial_ne_zero HighCore82229Upper_5_2.charFX
  from ProximityPrize.SubmissionLower.HighCore82229UpperGeometry

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
  have hd : ev (HighCore82229Upper_5_1.denominator J B) ≠ 0 := he.1
  have hb : ev (seedBiform B.denominator) ≠ 0 := by
    have h := hd
    rw [HighCore82229Upper_5_1.denominator, eval_denominator, mul_ne_zero_iff] at h
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
