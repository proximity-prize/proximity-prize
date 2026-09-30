import ProximityPrize.SubmissionLower.LowerFoundation
namespace ProximityPrize.SubmissionLower.RelativeContactOrder6814
open MvPolynomial ContactOrderBridge
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
variable (K : Type*) [Field K]

def xWeights : Fin 4 → ℕ := ![1,0,0,0]

theorem x_weight_blowup (d : Fin 4 →₀ ℕ) :
    Finsupp.weight xWeights (blowupExponent d) =
      Finsupp.weight diagonalWeights d := by
  rw [RCN081.weight_fin4, RCN081.weight_fin4]
  simp [xWeights, diagonalWeights, blowupExponent]

theorem atLeast_x_blowup (m : ℕ) (P : Poly4 K) :
    AtLeast xWeights m (contactBlowup K P) ↔ AtLeast diagonalWeights m P := by
  classical
  constructor
  · intro h d hd
    have hm : blowupExponent d ∈ (contactBlowup K P).support := by
      rw [support_contactBlowup]
      exact Finset.mem_image.mpr ⟨d,hd,rfl⟩
    simpa only [x_weight_blowup] using h _ hm
  · intro h d hd
    rw [support_contactBlowup] at hd
    obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hd
    simpa only [x_weight_blowup] using h e he

theorem atLeast_x_iff_dvd (m : ℕ) (P : Poly4 K) :
    AtLeast xWeights m P ↔
      Polynomial.X ^ m ∣ MvPolynomial.finSuccEquiv K 3 P := by
  classical
  rw [Polynomial.X_pow_dvd_iff]
  constructor
  · intro h n hn
    ext d
    rw [MvPolynomial.finSuccEquiv_coeff_coeff]
    by_contra hc
    have hw := h (Finsupp.cons n d) (MvPolynomial.mem_support_iff.mpr hc)
    rw [RCN081.weight_fin4] at hw
    simp [xWeights] at hw
    omega
  · intro h d hd
    by_contra hm
    have hm' : d 0 < m := by
      rw [RCN081.weight_fin4] at hm
      simpa [xWeights] using hm
    have hc := congrArg (MvPolynomial.coeff d.tail) (h (d 0) hm')
    rw [MvPolynomial.finSuccEquiv_coeff_coeff] at hc
    have he : Finsupp.cons (d 0) d.tail = d := by
      ext i
      fin_cases i <;> simp
    rw [he, MvPolynomial.coeff_zero] at hc
    exact MvPolynomial.mem_support_iff.mp hd hc

def contactPolynomial (x u0 u1 : K) :
    Poly4 K →+* Polynomial (MvPolynomial (Fin 3) K) :=
  (MvPolynomial.finSuccEquiv K 3).toRingHom.comp
    ((contactBlowup K).comp ((contactBlowup K).comp
      (localize K x u0 u1).toRingHom))

theorem contactAtLeast_iff_dvd (x u0 u1 : K) (m : ℕ) (P : Poly4 K) :
    ContactAtLeast K x u0 u1 m P ↔
      Polynomial.X ^ m ∣ contactPolynomial K x u0 u1 P := by
  change AtLeast localWeights m (localize K x u0 u1 P) ↔ _
  rw [← atLeast_contactBlowup_iff K m, ← atLeast_x_blowup K m,
    atLeast_x_iff_dvd K m]
  rfl

theorem blowup_ne_zero {P : Poly4 K} (hP : P ≠ 0) : contactBlowup K P ≠ 0 := by
  intro h
  have hs := congrArg MvPolynomial.support h
  rw [support_contactBlowup] at hs
  simp only [MvPolynomial.support_zero, Finset.image_eq_empty] at hs
  exact hP (MvPolynomial.support_eq_empty.mp hs)

def delocalize (x u0 u1 : K) : Poly4 K →ₐ[K] Poly4 K :=
  MvPolynomial.aeval ![MvPolynomial.X 0 - MvPolynomial.C x,
    MvPolynomial.X 1 - MvPolynomial.C u0 - MvPolynomial.X 3 * MvPolynomial.C u1 -
      MvPolynomial.X 2 * (MvPolynomial.X 0 - MvPolynomial.C x),
    MvPolynomial.X 2, MvPolynomial.X 3]

theorem delocalize_localize (x u0 u1 : K) (P : Poly4 K) :
    delocalize K x u0 u1 (localize K x u0 u1 P) = P := by
  have he : (delocalize K x u0 u1).comp (localize K x u0 u1) =
      AlgHom.id K (Poly4 K) := by
    ext i
    fin_cases i <;> simp [delocalize, localize, localVariables]
  exact DFunLike.congr_fun he P

theorem contactPolynomial_ne_zero (x u0 u1 : K) {P : Poly4 K} (hP : P ≠ 0) :
    contactPolynomial K x u0 u1 P ≠ 0 := by
  have hl : localize K x u0 u1 P ≠ 0 := by
    intro h
    have := congrArg (delocalize K x u0 u1) h
    rw [delocalize_localize, map_zero] at this
    exact hP this
  exact (map_ne_zero_iff _ (MvPolynomial.finSuccEquiv K 3).injective).mpr
    (blowup_ne_zero K (blowup_ne_zero K hl))

def contactOrder (x u0 u1 : K) (P : Poly4 K) : ℕ :=
  (contactPolynomial K x u0 u1 P).natTrailingDegree

theorem contactAtLeast_iff_le (x u0 u1 : K) (m : ℕ) (P : Poly4 K) (hP : P ≠ 0) :
    ContactAtLeast K x u0 u1 m P ↔ m ≤ contactOrder K x u0 u1 P := by
  rw [contactAtLeast_iff_dvd, Polynomial.X_pow_dvd_iff]
  constructor
  · intro h
    by_contra hm
    have hz := h (contactOrder K x u0 u1 P) (by omega)
    exact (Polynomial.coeff_natTrailingDegree_ne_zero.mpr
      (contactPolynomial_ne_zero K x u0 u1 hP)) hz
  · intro h n hn
    apply Polynomial.coeff_eq_zero_of_lt_natTrailingDegree
    exact lt_of_lt_of_le hn h

theorem contactOrder_mul (x u0 u1 : K) (P Q : Poly4 K) (hP : P ≠ 0) (hQ : Q ≠ 0) :
    contactOrder K x u0 u1 (P * Q) =
      contactOrder K x u0 u1 P + contactOrder K x u0 u1 Q := by
  unfold contactOrder
  rw [map_mul, Polynomial.natTrailingDegree_mul
    (contactPolynomial_ne_zero K x u0 u1 hP)
    (contactPolynomial_ne_zero K x u0 u1 hQ)]

theorem contact_mul_iff (x u0 u1 : K) (m : ℕ) (P Q : Poly4 K) (hP : P ≠ 0) :
    ContactAtLeast K x u0 u1 m (P * Q) ↔
      ContactAtLeast K x u0 u1 (m - contactOrder K x u0 u1 P) Q := by
  by_cases hQ : Q = 0
  · subst Q
    simp [ContactAtLeast, AtLeast]
  rw [contactAtLeast_iff_le K x u0 u1 m _ (mul_ne_zero hP hQ),
    contactAtLeast_iff_le K x u0 u1 _ Q hQ, contactOrder_mul K x u0 u1 P Q hP hQ]
  omega

end
end ProximityPrize.SubmissionLower.RelativeContactOrder6814
