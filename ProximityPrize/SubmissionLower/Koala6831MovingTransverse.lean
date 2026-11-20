import ProximityPrize.SubmissionLower.Koala6831MovingDerivation

namespace ProximityPrize.SubmissionLower.Koala6831Moving

noncomputable section

section StripLinearFactor

variable {E : Type*} [CommRing E] [IsDomain E] {p : ℕ} [CharP E p]

theorem eq_constant_of_derivative_eq_zero_of_degree_lt
    {H : Polynomial E} (hdeg : H.natDegree < p) (hderiv : H.derivative = 0) :
    H = Polynomial.C (H.coeff 0) := by
  apply Polynomial.eq_C_of_natDegree_eq_zero
  by_contra hpos
  have hn : 1 ≤ H.natDegree := Nat.pos_of_ne_zero hpos
  have hH : H ≠ 0 := by
    intro h
    exact hpos (by simp [h])
  have hcoeff : H.coeff H.natDegree ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hH
  have hcast : (H.natDegree : E) ≠ 0 := by
    intro h
    exact (Nat.not_le_of_gt hdeg)
      (Nat.le_of_dvd hn ((CharP.cast_eq_zero_iff E p H.natDegree).mp h))
  apply mul_ne_zero hcoeff hcast
  have h := congrArg (fun G : Polynomial E => G.coeff (H.natDegree - 1)) hderiv
  have hcastAdd : (↑(H.natDegree - 1) : E) + 1 = ↑H.natDegree := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      congrArg (fun i : ℕ => (i : E)) (Nat.sub_add_cancel hn)
  simpa only [Polynomial.coeff_derivative, Nat.sub_add_cancel hn, hcastAdd,
    Polynomial.coeff_zero] using h

theorem eq_constant_of_dvd_derivative_of_degree_lt
    {H : Polynomial E} (hdeg : H.natDegree < p) (hdvd : H ∣ H.derivative) :
    H = Polynomial.C (H.coeff 0) := by
  apply eq_constant_of_derivative_eq_zero_of_degree_lt hdeg
  by_contra hn
  have hpos : H.natDegree ≠ 0 := fun h => hn (Polynomial.derivative_of_natDegree_zero h)
  exact (not_lt_of_ge (Polynomial.natDegree_le_of_dvd hdvd hn))
    (Polynomial.natDegree_derivative_lt hpos)

theorem pow_mul_constant_of_dvd_linear_sq_mul_derivative
    [DecompositionMonoid (Polynomial E)]
    (a : E) {H : Polynomial E} (hH : H ≠ 0) (hdeg : H.natDegree < p)
    (hdvd : H ∣ (Polynomial.X - Polynomial.C a)^2 * H.derivative) :
    ∃ n : ℕ, ∃ c : E, H = (Polynomial.X - Polynomial.C a)^n * Polynomial.C c := by
  let ell : Polynomial E := Polynomial.X - Polynomial.C a
  let n := H.rootMultiplicity a
  obtain ⟨G, hfactor, hnot⟩ := H.exists_eq_pow_rootMultiplicity_mul_and_not_dvd hH a
  change H = ell^n * G at hfactor
  change ¬ell ∣ G at hnot
  have hGdeg : G.natDegree < p :=
    (Polynomial.natDegree_le_of_dvd (hfactor ▸ dvd_mul_left G (ell^n)) hH).trans_lt hdeg
  have htotal : ell^n * G ∣ ell^2 * ((ell^n).derivative * G + ell^n * G.derivative) := by
    change H ∣ ell^2 * H.derivative at hdvd
    rw [hfactor, Polynomial.derivative_mul] at hdvd
    exact hdvd
  have hpowDiff : ell^n ∣ ell^2 * (ell^n).derivative := by
    calc
      ell^n ∣ ell^(2 + (n - 1)) := pow_dvd_pow ell (by omega)
      _ ∣ ell^2 * (ell^n).derivative := by
        rw [pow_add]
        exact mul_dvd_mul_left _ (Polynomial.pow_sub_one_dvd_derivative_of_pow_dvd dvd_rfl)
  have hfirst : ell^n * G ∣ ell^2 * ((ell^n).derivative * G) := by
    rw [← mul_assoc]
    simpa only [mul_comm G] using mul_dvd_mul_left G hpowDiff
  have hsecond : ell^n * G ∣ ell^2 * (ell^n * G.derivative) := by
    rw [mul_add] at htotal
    have h := dvd_sub htotal hfirst
    simpa only [add_sub_cancel_left] using h
  have hstrip : G ∣ ell^2 * G.derivative := by
    apply (dvd_cancel_left_mem_nonZeroDivisors
      ((Polynomial.monic_X_sub_C a).pow n).mem_nonZeroDivisors).mp
    rw [mul_left_comm (ell^n) (ell^2)]
    exact hsecond
  have hrel : IsRelPrime ell G :=
    (Polynomial.prime_X_sub_C a).irreducible.isRelPrime_iff_not_dvd.mpr hnot
  have hGderiv : G ∣ G.derivative := hrel.symm.pow_right.dvd_of_dvd_mul_left hstrip
  exact ⟨n, G.coeff 0, hfactor.trans
    (congrArg (fun J : Polynomial E => ell^n * J)
      (eq_constant_of_dvd_derivative_of_degree_lt hGdeg hGderiv))⟩

end StripLinearFactor

end

end ProximityPrize.SubmissionLower.Koala6831Moving
