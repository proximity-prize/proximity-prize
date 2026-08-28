import ProximityPrize.SubmissionLower.BCHKSFrobeniusArithmetic6400

/-!
# The two-relation finish for the Frobenius pivot

Two independent multiplier relations rationalize both rows of the received
line.  Cramer's rule then turns every close polynomial into the same affine
polynomial pencil.  This file isolates that finish from the outstanding
Toeplitz classification theorem.
-/

namespace ProximityPrize.SubmissionLower

open Polynomial

set_option maxRecDepth 100000

variable {F : Type} [Field F] [DecidableEq F]

/-- Agreement on more points than the degrees of both polynomials gives a
polynomial identity. -/
theorem polynomial_eq_of_finset_evals
    (P Q : F[X]) (E : Finset F)
    (hP : P.natDegree < E.card) (hQ : Q.natDegree < E.card)
    (heval : ∀ x ∈ E, P.eval x = Q.eval x) : P = Q := by
  apply Polynomial.eq_of_natDegree_lt_card_of_eval_eq P Q
    (f := fun x : {x // x ∈ E} => (x : F)) Subtype.val_injective
  · intro x
    exact heval x x.property
  · simpa [Fintype.card_coe] using max_lt hP hQ

/-- Two independent polynomial multiplier relations force a whole selected
family of close polynomials onto one affine line.

The hypotheses `hleftDegree` and `hrightDegree` are the only place where the
Reed--Solomon degree ledger enters.  At the score-64 endpoint both are below
`k + 2*h`, while every `E z` has `k + 2*h + 9316` points. -/
theorem affine_family_of_two_multiplier_relations
    (T : Finset F) (E : F → Finset F)
    (P : F → F[X]) (U₀ U₁ : F → F)
    (q₀ r₀ q₁ r₁ C₀ C₁ : F[X]) (k : ℕ)
    (z₀ z₁ : F) (hz₀ : z₀ ∈ T) (hz₁ : z₁ ∈ T) (hzne : z₀ ≠ z₁)
    (hPdegree : ∀ z ∈ T, (P z).natDegree < k)
    (hrel₀ : ∀ x : F,
      q₀.eval x * U₀ x + r₀.eval x * U₁ x = C₀.eval x)
    (hrel₁ : ∀ x : F,
      q₁.eval x * U₀ x + r₁.eval x * U₁ x = C₁.eval x)
    (hagree : ∀ z ∈ T, ∀ x ∈ E z,
      (P z).eval x = U₀ x + z * U₁ x)
    (hdet : q₀ * r₁ - q₁ * r₀ ≠ 0)
    (hleftDegree : ∀ z ∈ T,
      ((q₀ * r₁ - q₁ * r₀) * P z).natDegree < (E z).card)
    (hrightDegree : ∀ z ∈ T,
      ((r₁ * C₀ - r₀ * C₁) +
        Polynomial.C z * (q₀ * C₁ - q₁ * C₀)).natDegree < (E z).card) :
    ∃ p₀ p₁ : F[X], p₀.natDegree < k ∧ p₁.natDegree < k ∧
      ∀ z ∈ T, P z = p₀ + Polynomial.C z * p₁ := by
  let Δ : F[X] := q₀ * r₁ - q₁ * r₀
  let A : F[X] := r₁ * C₀ - r₀ * C₁
  let B : F[X] := q₀ * C₁ - q₁ * C₀
  have hidentity : ∀ z ∈ T,
      Δ * P z = A + Polynomial.C z * B := by
    intro z hz
    apply polynomial_eq_of_finset_evals
    · simpa [Δ] using hleftDegree z hz
    · simpa [A, B] using hrightDegree z hz
    · intro x hx
      rw [Polynomial.eval_mul, hagree z hz x hx]
      simp only [A, B, Δ, Polynomial.eval_add, Polynomial.eval_sub,
        Polynomial.eval_mul, Polynomial.eval_C]
      linear_combination
        r₁.eval x * hrel₀ x - r₀.eval x * hrel₁ x +
          z * (q₀.eval x * hrel₁ x - q₁.eval x * hrel₀ x)
  let p₁ : F[X] :=
    Polynomial.C ((z₁ - z₀)⁻¹) * (P z₁ - P z₀)
  let p₀ : F[X] := P z₀ - Polynomial.C z₀ * p₁
  have hscalar : (z₁ - z₀)⁻¹ * (z₁ - z₀) = 1 := by
    rw [inv_mul_cancel₀]
    exact sub_ne_zero.mpr hzne.symm
  have hΔp₁ : Δ * p₁ = B := by
    have hdiff : Δ * (P z₁ - P z₀) = Polynomial.C (z₁ - z₀) * B := by
      calc
        Δ * (P z₁ - P z₀) = Δ * P z₁ - Δ * P z₀ := by ring
        _ = (A + Polynomial.C z₁ * B) -
            (A + Polynomial.C z₀ * B) := by
              rw [hidentity z₁ hz₁, hidentity z₀ hz₀]
        _ = (Polynomial.C z₁ - Polynomial.C z₀) * B := by ring
        _ = Polynomial.C (z₁ - z₀) * B := by rw [Polynomial.C_sub]
    calc
      Δ * p₁ = Polynomial.C ((z₁ - z₀)⁻¹) *
          (Δ * (P z₁ - P z₀)) := by simp only [p₁]; ring
      _ = Polynomial.C ((z₁ - z₀)⁻¹) *
          (Polynomial.C (z₁ - z₀) * B) := by rw [hdiff]
      _ = B := by rw [← mul_assoc, ← Polynomial.C_mul, hscalar]; simp
  have hΔp₀ : Δ * p₀ = A := by
    rw [show Δ * p₀ = Δ * P z₀ - Polynomial.C z₀ * (Δ * p₁) by
      simp only [p₀]; ring, hidentity z₀ hz₀, hΔp₁]
    ring
  have hp₁degree : p₁.natDegree < k := by
    exact (Polynomial.natDegree_C_mul_le _ _).trans_lt
      ((Polynomial.natDegree_sub_le _ _).trans_lt
        (max_lt (hPdegree z₁ hz₁) (hPdegree z₀ hz₀)))
  have hp₀degree : p₀.natDegree < k := by
    exact (Polynomial.natDegree_sub_le _ _).trans_lt
      (max_lt (hPdegree z₀ hz₀)
        ((Polynomial.natDegree_C_mul_le _ _).trans_lt hp₁degree))
  refine ⟨p₀, p₁, hp₀degree, hp₁degree, ?_⟩
  intro z hz
  have hzero : Δ * (P z - (p₀ + Polynomial.C z * p₁)) = 0 := by
    rw [mul_sub, mul_add, hidentity z hz, hΔp₀]
    rw [show Δ * (Polynomial.C z * p₁) =
      Polynomial.C z * (Δ * p₁) by ring, hΔp₁]
    ring
  exact sub_eq_zero.mp ((mul_eq_zero.mp hzero).resolve_left (by simpa [Δ] using hdet))

end ProximityPrize.SubmissionLower
