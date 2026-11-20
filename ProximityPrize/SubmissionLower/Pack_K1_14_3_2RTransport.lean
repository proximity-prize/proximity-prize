import Mathlib.Algebra.MvPolynomial.Coeff
import Mathlib.Algebra.TrivSqZeroExt.Ideal
import Mathlib.LinearAlgebra.FreeModule.Norm
import Mathlib.NumberTheory.RatFunc.Ostrowski
import Mathlib.RingTheory.Artinian.Algebra
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.Localization.NormTrace
import ProximityPrize.SubmissionLower.Pack_K1Defs
import ProximityPrize.SubmissionLower.Fast023
import ProximityPrize.SubmissionLower.Fast029
import ProximityPrize.SubmissionLower.Pack_K1_14_2_2_4Split
set_option Elab.async false

section PackSource_K1_14_3_2RTransport
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
set_option maxHeartbeats 1500000

namespace K1_14_3_2R

noncomputable section

open K1 K1_14 K1_14_3 Polynomial

private abbrev Parameters := MvPolynomial (Fin 4) FX
private abbrev Whole := MvPolynomial (Fin 2) Parameters
private abbrev Sloped := MvPolynomial (Fin 2) Jet
private abbrev par (i : Fin 4) : Whole := MvPolynomial.C (MvPolynomial.X i)
private abbrev free (i : Fin 2) : Whole := MvPolynomial.X i

private abbrev t (i : Fin 2) : Jet := C (C (MvPolynomial.X i))
private abbrev y : Jet := C (Polynomial.X (R := Seeds))
private abbrev v : Jet := Polynomial.X (R := Equation)
private abbrev scalar : FX →+* Jet := C.comp (C.comp MvPolynomial.C)

theorem jetHom_ext {A : Type*} [CommRing A] {f g : Jet →+* A}
    (hC : ∀ a, f (scalar a) = g (scalar a))
    (ht : ∀ i, f (t i) = g (t i)) (hy : f y = g y) (hv : f v = g v) : f = g :=
  Polynomial.ringHom_ext' (Polynomial.ringHom_ext' (MvPolynomial.ringHom_ext hC ht) hy) hv

private def positions (s : Slice) : Fin 4 → Whole :=
  match s with
  | .seed => ![par 2, par 3, free 0, free 1]
  | .ordinate => ![par 2 - par 0 * free 0, free 0, par 3, free 1]
  | .mixed => ![par 2 - par 0 * free 0, free 0, par 3 - par 1 * free 1, free 1]
  | .jets => ![free 0, free 1, par 2, par 3]

private def raw (s : Slice) : Jet →+* Whole :=
  let z := positions s
  eval₂RingHom (eval₂RingHom (MvPolynomial.eval₂Hom (MvPolynomial.C.comp MvPolynomial.C)
    ![z 0, z 1]) (z 2)) (z 3)

private def forward (s : Slice) : Sloped →+* Whole :=
  MvPolynomial.eval₂Hom (raw s) ![par 0, par 1]

private abbrev slope (i : Fin 2) : Sloped := MvPolynomial.X i
private abbrev co : Jet →+* Sloped := MvPolynomial.C
private def offsets (s : Slice) : Fin 4 → Sloped :=
  let st := co (t 0) + slope 0 * co (t 1)
  let jy := co y + slope 1 * co v
  match s with
  | .seed => ![slope 0, slope 1, co (t 0), co (t 1)]
  | .ordinate => ![slope 0, slope 1, st, co y]
  | .mixed => ![slope 0, slope 1, st, jy]
  | .jets => ![slope 0, slope 1, co y, co v]

private def other (s : Slice) : Fin 2 → Sloped :=
  match s with
  | .seed => ![co y, co v]
  | .ordinate | .mixed => ![co (t 1), co v]
  | .jets => ![co (t 0), co (t 1)]

private def backward (s : Slice) : Whole →+* Sloped :=
  MvPolynomial.eval₂Hom (MvPolynomial.eval₂Hom (co.comp scalar) (offsets s)) (other s)

private theorem forward_backward (s : Slice) :
    (forward s).comp (backward s) = RingHom.id _ := by
  apply MvPolynomial.ringHom_ext'
  · apply MvPolynomial.ringHom_ext
    · intro a
      simp [forward, backward, raw, scalar]
    · intro i
      cases s <;> fin_cases i <;>
        simp [forward, backward, raw, positions, offsets, other, t, y, v, co, slope, par, free]
  · intro i
    cases s <;> fin_cases i <;>
      simp [forward, backward, raw, positions, offsets, other, t, y, v, co, slope, par, free]

private theorem backward_forward (s : Slice) :
    (backward s).comp (forward s) = RingHom.id _ := by
  apply MvPolynomial.ringHom_ext'
  · apply jetHom_ext
    · intro a
      simp [forward, backward, raw, scalar]
    · intro i
      cases s <;> fin_cases i <;>
        simp [forward, backward, raw, positions, offsets, other, t, y, v, co, slope, par, free]
    · cases s <;>
        simp [forward, backward, raw, positions, offsets, other, t, y, v, co, slope, par, free]
    · cases s <;>
        simp [forward, backward, raw, positions, offsets, other, t, y, v, co, slope, par, free]
  · intro i
    cases s <;> fin_cases i <;>
      simp [forward, backward, raw, positions, offsets, other, t, y, v, co, slope, par, free]

private def coordinateEquiv (s : Slice) : Sloped ≃+* Whole :=
  RingEquiv.ofRingHom (forward s) (backward s) (forward_backward s) (backward_forward s)

/-- Before inverting the parameter denominators, the sliced ring is obtained
by adjoining just the two independent line slopes to the original jet ring. -/
private theorem raw_prime (s : Slice) (q : Surface) :
    (q.asIdeal.map (raw s)).IsPrime ∧ (q.asIdeal.map (raw s)).comap (raw s) = q.asIdeal := by
  let e := coordinateEquiv s
  have eqraw : raw s = e.toRingHom.comp co := by
    apply RingHom.ext
    intro a
    change raw s a = forward s (MvPolynomial.C a)
    simp [forward]
  have eqco : q.asIdeal.map co = RingHom.ker (MvPolynomial.map (σ := Fin 2) (Ideal.Quotient.mk q.asIdeal)) := by
    rw [MvPolynomial.ker_map, Ideal.mk_ker]
  have hp : (q.asIdeal.map co).IsPrime := eqco ▸ RingHom.ker_isPrime _
  have hc : (q.asIdeal.map co).comap co = q.asIdeal := by
    ext a
    constructor
    · intro ha
      exact (by simpa using (MvPolynomial.mem_map_C_iff.mp (show co a ∈ q.asIdeal.map co from ha) 0))
    · intro ha
      exact Ideal.mem_map_of_mem co ha
  rw [eqraw, ← Ideal.map_map, ← Ideal.comap_comap, Ideal.comap_map_of_bijective e.toRingHom e.bijective]
  exact ⟨Ideal.map_isPrime_of_equiv e, hc⟩

attribute [local instance] MvPolynomial.algebraMvPolynomial

def sectionChart (s : Slice) : Jet →+* MvPolynomial (Fin 2) SectionField :=
  (MvPolynomial.map (algebraMap Parameters SectionField)).comp (raw s)

/-- Localization may remove the component. Every surviving prime contracts
exactly through the chart and the polynomial extension. -/
theorem localized_prime (s : Slice) (q : Surface) :
    q.asIdeal.map (sectionChart s) = ⊤ ∨ (q.asIdeal.map (sectionChart s)).IsPrime ∧
      (q.asIdeal.map (sectionChart s)).comap (sectionChart s) = q.asIdeal := by
  let B := MvPolynomial (Fin 2) SectionField
  let M := (nonZeroDivisors Parameters).map (MvPolynomial.C (σ := Fin 2))
  let I := q.asIdeal.map (raw s)
  obtain ⟨hp, hc⟩ := raw_prime s q
  unfold sectionChart
  rw [← Ideal.map_map]
  change I.map (algebraMap Whole B) = ⊤ ∨ (I.map (algebraMap Whole B)).IsPrime ∧
    (I.map (algebraMap Whole B)).comap ((algebraMap Whole B).comp (raw s)) = q.asIdeal
  by_cases ht : I.map (algebraMap Whole B) = ⊤
  · exact Or.inl ht
  right
  have hd := (IsLocalization.map_algebraMap_ne_top_iff_disjoint M B I).mp ht
  refine ⟨IsLocalization.isPrime_of_isPrime_disjoint M B I hp hd, ?_⟩
  rw [← Ideal.comap_comap]
  exact (congrArg (Ideal.comap (raw s)) (IsLocalization.under_map_of_isPrime_disjoint M B hp hd)).trans hc

end
end K1_14_3_2R
end PackSource_K1_14_3_2RTransport
