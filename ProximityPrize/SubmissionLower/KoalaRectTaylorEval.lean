import ProximityPrize.SubmissionLower.KoalaRectTaylorSections

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000

namespace KoalaRectTaylor
noncomputable section

open P1 (I)
open K1_14 (FX)
open HighCore82219Upper (Input ResidueLift Factors)
open HighCore82219Upper_3 (JetRing graphIdeal jetDenominator oldDenominator oldNumerator
  residueInJet openFactor)
open HighCore82219Upper_3_3 (residueCut residueValue canonicalJet curveValue FixedWeights
  prefixLength prefixIndex sectionIndex wordAt)
open private HighCore82219Upper_3.oldDenominator_eq
  from ProximityPrize.SubmissionLower.HighCore82219UpperGeometry
open HighCore82219Upper_3 (oldDenominator_eq)
open scoped BigOperators

variable {E : Type} [Field E] [Algebra FX E]

theorem open_denominator {J : Input} {B : ResidueLift J} (φ : JetRing →ₐ[FX] E)
    (hu : φ (openFactor J B) ≠ 0) (j : ℕ) :
    φ (residueInJet B * Polynomial.C J.f.derivative^j) ≠ 0 := by
  rw [openFactor,map_mul,mul_ne_zero_iff] at hu
  rw [map_mul,map_pow]
  exact mul_ne_zero hu.1 (pow_ne_zero _ hu.2)

theorem taylor_ratio {J : Input} {B : ResidueLift J} {D : Factors J B}
    (φ : JetRing →ₐ[FX] E) (hu : φ (openFactor J B) ≠ 0)
    (hg : ∀ p ∈ graphIdeal J B D, φ p = 0) {r j : ℕ} (hj : j ≤ r) :
    φ (taylorNumerator J B r j) / φ (jetDenominator J B r) =
      φ (oldNumerator J B j) / φ (oldDenominator J B j) := by
  have hd : φ (jetDenominator J B r) ≠ 0 := open_denominator φ hu _
  have ho : φ (oldDenominator J B j) ≠ 0 := by
    rw [oldDenominator_eq]
    exact open_denominator φ hu _
  have h := hg _ (taylor_agrees J B D hj)
  rw [map_sub,map_mul,map_mul,sub_eq_zero,mul_comm (φ (oldDenominator J B j))] at h
  exact (div_eq_div_iff hd ho).mpr h

theorem residue_ratio {J : Input} {B : ResidueLift J} (φ : JetRing →ₐ[FX] E)
    (hu : φ (openFactor J B) ≠ 0) (r : ℕ) (x : I) :
    φ (residueCut J B r x) / φ (jetDenominator J B r) = residueValue φ B x := by
  rw [residueValue]
  apply (div_eq_div_iff (open_denominator φ hu _)
    (by simpa only [pow_zero,mul_one] using open_denominator φ hu 0)).mpr
  simp only [residueCut,map_mul,map_pow]
  ring

theorem node_evaluation {J : Input} {B : ResidueLift J} {D : Factors J B}
    (φ : JetRing →ₐ[FX] E) (hu : φ (openFactor J B) ≠ 0)
    (hg : ∀ p ∈ graphIdeal J B D, φ p = 0)
    (sites : Finset I) (x : I) (b : I → FX) (a : Fin (prefixLength J sites) → FX)
    (hw : FixedWeights J sites x b a)
    (hs : ∀ i ∈ sites, curveValue φ J B i = algebraMap FX E (wordAt J i)) :
    φ (nodeNumerator J B sites x b a) / φ (jetDenominator J B (J.ell-sites.card)) =
      curveValue φ J B x - algebraMap FX E (wordAt J x) := by
  classical
  have hd : φ (jetDenominator J B (J.ell-sites.card)) ≠ 0 := open_denominator φ hu _
  have ht (j : Fin (prefixLength J sites)) :
      φ (taylorNumerator J B (J.ell-sites.card) (sectionIndex J sites j).val) /
        φ (jetDenominator J B (J.ell-sites.card)) = canonicalJet φ J B (prefixIndex J sites j) :=
    taylor_ratio (D := D) φ hu hg (Nat.le_of_lt_succ (sectionIndex J sites j).isLt)
  have heval (s : FX) (q : JetRing) : φ (s • q) = algebraMap FX E s * φ q := by
    rw [Algebra.smul_def,map_mul,AlgHom.commutes]
  simp only [nodeNumerator,map_add,map_sub,map_sum,heval,add_div,sub_div,Finset.sum_div,
    mul_div_assoc,div_self hd,mul_one,residue_ratio φ hu,ht]
  exact (hw E (residueValue φ B) (canonicalJet φ J B) hs).symm

theorem node_zero_iff {J : Input} {B : ResidueLift J} {D : Factors J B}
    (φ : JetRing →ₐ[FX] E) (hu : φ (openFactor J B) ≠ 0)
    (hg : ∀ p ∈ graphIdeal J B D, φ p = 0)
    {sites : Finset I} {x : I} {b : I → FX} {a : Fin (prefixLength J sites) → FX}
    (hw : FixedWeights J sites x b a)
    (hs : ∀ i ∈ sites, curveValue φ J B i = algebraMap FX E (wordAt J i)) :
    φ (nodeNumerator J B sites x b a) = 0 ↔ curveValue φ J B x = algebraMap FX E (wordAt J x) := by
  have h := node_evaluation φ hu hg sites x b a hw hs
  constructor
  · intro hz
    rw [hz,zero_div] at h
    exact sub_eq_zero.mp h.symm
  · intro hx
    rw [hx,sub_self] at h
    exact (div_eq_zero_iff.mp h).resolve_right (open_denominator φ hu _)

end
end KoalaRectTaylor

