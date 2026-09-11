import ProximityPrize.SubmissionLower.PartG036


section Compact_SecondJetCoefficients
/-! Viewing the interpolant as a polynomial in its second derivative variable.
Coefficient variables are X, Y, R, Z. -/
namespace ProximityPrize.SubmissionLower.SecondJetCoefficients
open MvPolynomial SecondJetSupport
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
variable {K : Type*} [Field K]

def asS : Poly (K := K) ≃ₐ[K] Polynomial (MvPolynomial (Fin 4) K) :=
  (MvPolynomial.renameEquiv K (Equiv.swap (0 : Fin 5) 1)).trans (MvPolynomial.finSuccEquiv K 4)

def liftExponent (j : ℕ) (d : Fin 4 →₀ ℕ) : Fin 5 →₀ ℕ :=
  Finsupp.mapDomain (Equiv.swap (0 : Fin 5) 1) (d.cons j)

theorem swap_lift (j : ℕ) (d : Fin 4 →₀ ℕ) :
    Finsupp.mapDomain (Equiv.swap (0 : Fin 5) 1) (liftExponent j d) = d.cons j := by
  ext i
  simp [liftExponent, Finsupp.mapDomain_equiv_apply]

theorem lift_coordinates (j : ℕ) (d : Fin 4 →₀ ℕ) :
    liftExponent j d 0 = d 0 ∧ liftExponent j d 1 = j ∧
      liftExponent j d 2 = d 1 ∧ liftExponent j d 3 = d 2 ∧ liftExponent j d 4 = d 3 := by
  simp [liftExponent, Finsupp.mapDomain_equiv_apply, Equiv.swap_apply_def, Fin.ext_iff]
  exact ⟨rfl,rfl,rfl,rfl⟩

theorem asS_coeff (P : Poly (K := K)) (j : ℕ) (d : Fin 4 →₀ ℕ) :
    MvPolynomial.coeff d ((asS (K := K) P).coeff j) =
      MvPolynomial.coeff (liftExponent j d) P := by
  change MvPolynomial.coeff d (((MvPolynomial.finSuccEquiv K 4)
    (MvPolynomial.rename (Equiv.swap (0 : Fin 5) 1) P)).coeff j) = _
  rw [MvPolynomial.finSuccEquiv_coeff_coeff, ← swap_lift j d,
    MvPolynomial.coeff_rename_mapDomain _ (Equiv.swap (0 : Fin 5) 1).injective]

theorem coefficient_support (P : Poly (K := K)) (j : ℕ) (d : Fin 4 →₀ ℕ)
    (hd : d ∈ ((asS (K := K) P).coeff j).support) : liftExponent j d ∈ P.support := by
  simpa only [MvPolynomial.mem_support_iff, asS_coeff] using hd

theorem coefficient_bounds (P : Poly (K := K))
    (hP : ∀ e ∈ P.support, e 1+e 3 ≤ 39 ∧ e 1 ≤ 18 ∧ e 1+e 2+e 3+e 4 ≤ 2160 ∧
      e 0+131071*e 2+131070*e 3+131069*e 1 < 21611508)
    (j : ℕ) (d : Fin 4 →₀ ℕ) (hd : d ∈ ((asS (K := K) P).coeff j).support) :
    j ≤ 18 ∧ j+d 2 ≤ 39 ∧ j+d 1+d 2 ≤ 164 ∧ j+d 1+d 2+d 3 ≤ 2160 := by
  have hh := hP _ (coefficient_support P j d hd)
  obtain ⟨h0,h1,h2,h3,h4⟩ := lift_coordinates j d
  rw [h0,h1,h2,h3,h4] at hh
  omega

end
end ProximityPrize.SubmissionLower.SecondJetCoefficients

end Compact_SecondJetCoefficients
