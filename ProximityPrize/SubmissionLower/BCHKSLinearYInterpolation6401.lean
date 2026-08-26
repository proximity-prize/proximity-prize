import ProximityPrize.SubmissionLower.BCHKSConcreteGSLinearY6401
import ProximityPrize.SubmissionLower.BCHKSLinearYKernelAudit6401

namespace ProximityPrize.SubmissionLower
namespace BCHKSLinearYInterpolation6401

open Polynomial
open BCHKSSubstitutionVanish
open BCHKSLinearYKernelAudit6401

set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

/-!
# Full-domain score-64.01 interpolation with a small residual

Unlike the score-64.00 interpolants, the substituted polynomial need not be
zero: its weighted `X` cap is `196608`, while an owner supplies only `185354`
roots.  The useful exact output is the agreement locator times a polynomial
of degree at most `11253`.
-/

theorem exists_linearY_interpolant_residual6401
    {F : Type} [Field F] [DecidableEq F]
    (omega : Fin BCHKSConcreteGSLinearY6401.n ↪ F)
    (u₀ u₁ : Fin BCHKSConcreteGSLinearY6401.n → F)
    (T : Finset F) (P : T → F[X])
    (Arow : T → Finset (Fin BCHKSConcreteGSLinearY6401.n))
    (hPdegree : ∀ z : T, (P z).natDegree ≤ 131071)
    (hrow : ∀ z : T, 185354 ≤ (Arow z).card)
    (hmatch : ∀ z : T, ∀ i ∈ Arow z,
      (P z).eval (omega i) = u₀ i + (z : F) * u₁ i) :
    ∃ Q : Polynomial (Polynomial (Polynomial F)),
      Q ≠ 0 ∧
      (∀ j x, (Q.coeff j).coeff x ≠ 0 →
        j < 2 ∧ x + 131071 * j < 196608 ∧
          ((Q.coeff j).coeff x).natDegree + j < 65538) ∧
      (∀ z : T, ∃ E : F[X],
        triEval Q (z : F) (P z) =
          (∏ i ∈ Arow z,
            (Polynomial.X - Polynomial.C (omega i))) * E ∧
        E.natDegree ≤ 11253) := by
  classical
  obtain ⟨Q, hQ, hvan, hcaps⟩ :=
    BCHKSConcreteGSLinearY6401.exists_interpolant omega u₀ u₁
  refine ⟨Q, hQ, ?_, ?_⟩
  · intro j x hx
    have h := hcaps j x hx
    norm_num [BCHKSConcreteGSLinearY6401.DY,
      BCHKSConcreteGSLinearY6401.DX,
      BCHKSConcreteGSLinearY6401.k,
      BCHKSConcreteGSLinearY6401.DZ] at h ⊢
    exact h
  · intro z
    let yZ : Fin BCHKSConcreteGSLinearY6401.n → F[X] := fun i ↦
      Polynomial.C (u₀ i) + Polynomial.X * Polynomial.C (u₁ i)
    apply exists_linearY_locator_residual_of_support6401
      Q (z : F) (P z) omega (Arow z) yZ
  
    · simpa [a6401, bchksAgreements6401] using hrow z
    · intro i hi s t d hst
      dsimp [yZ]
      have hh := hvan i s t (by
        simpa [multiplicity6401, BCHKSConcreteGSLinearY6401.m] using hst)
      have hd := Polynomial.ext_iff.mp hh d
      simpa only [Polynomial.coeff_zero] using hd
    · intro i hi
      rw [hmatch z i hi]
      simp [yZ]
      ring
    · simpa [k6401] using hPdegree z
    · intro j x hx
      have h := hcaps j x hx
      norm_num [yCap6401, xCap6401, k6401, zCap6401,
        BCHKSConcreteGSLinearY6401.DY,
        BCHKSConcreteGSLinearY6401.DX,
        BCHKSConcreteGSLinearY6401.k,
        BCHKSConcreteGSLinearY6401.DZ] at h ⊢
      exact h

end BCHKSLinearYInterpolation6401
end ProximityPrize.SubmissionLower
