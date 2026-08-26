import ProximityPrize.SubmissionLower.BCHKSConcreteGSFresh6400
import ProximityPrize.SubmissionLower.BCHKSSubstitutionVanish
namespace ProximityPrize.SubmissionLower
namespace BCHKSFreshQuotientInterpolation6400
open Polynomial
open BCHKSConcreteGSFresh6400
open BCHKSSubstitutionVanish
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000
theorem exists_freshQuotient_interpolant_vanishing6400
    {F : Type} [Field F] [DecidableEq F]
    (omega : Fin 241914 ↪ F) (u₀ u₁ : Fin 241914 → F)
    (T : Finset F) (P : T → F[X])
    (Arow : T → Finset (Fin 241914))
    (hPdegree : ∀ z : T, (P z).natDegree ≤ 110841)
    (hrow : ∀ z : T, 165134 ≤ (Arow z).card)
    (hmatch : ∀ z : T, ∀ i ∈ Arow z,
      (P z).eval (omega i) = u₀ i + (z : F) * u₁ i) :
    ∃ Q : Polynomial (Polynomial (Polynomial F)),
      Q ≠ 0 ∧
      (∀ z : T, BCHKSSubstitutionVanish.triEval Q (z : F) (P z) = 0) ∧
      (∀ j a, (Q.coeff j).coeff a ≠ 0 →
        j < 42 ∧ a + 110841 * j < 4623752 ∧
          ((Q.coeff j).coeff a).natDegree + j < 836) := by
  classical
  obtain ⟨Q, hQ, hvan, hcaps⟩ :=
    BCHKSConcreteGSFresh6400.exists_interpolant omega u₀ u₁
  refine ⟨Q, hQ, ?_, hcaps⟩
  intro z
  apply triEval_eq_zero_of_many_shift_vanishing_of_weighted_X_cap
    Q (z : F) (P z) omega (Arow z)
      (fun i ↦ Polynomial.C (u₀ i) +
        Polynomial.X * Polynomial.C (u₁ i))
      28 110841 4623751
  · intro i hi s t h hst
    have hz := congrArg (fun p : F[X] ↦ p.coeff h)
      (hvan i s t hst)
    exact hz
  · intro i hi
    rw [hmatch z i hi]
    simp
    ring
  · exact hPdegree z
  · intro j a hja
    have hc := hcaps j a hja
    norm_num [BCHKSConcreteGSFresh6400.DY,
      BCHKSConcreteGSFresh6400.DX,
      BCHKSConcreteGSFresh6400.k,
      BCHKSConcreteGSFresh6400.DZ] at hc
    omega
  · have hc := hrow z
    omega
end BCHKSFreshQuotientInterpolation6400
end ProximityPrize.SubmissionLower
