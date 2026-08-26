import ProximityPrize.SubmissionLower.BCHKSExtremePrimitiveTerminalFixedPairOrbit6401
import ProximityPrize.SubmissionLower.BCHKSFrobeniusLinearPairNoGo6401
import ProximityPrize.SubmissionLower.BCHKSFrobeniusHighSupportResidual6401
import ProximityPrize.SubmissionLower.BCHKSSubfieldFrobenius6401
namespace ProximityPrize.SubmissionLower
namespace BCHKSExtremePrimitiveFixedPairSlopeDescentNoGo6401
open Polynomial
open BCHKSFrobeniusPrimitiveCleanup6401
open BCHKSFrobeniusLinearPairNoGo6401
open BCHKSFrobeniusHighSupportResidual6401
open BCHKSSubfieldFrobenius6401
set_option maxHeartbeats 3000000
set_option maxRecDepth 1000000
section CorrectedSlopeDescent
variable {F I : Type*} [Field F] [Fintype I] [DecidableEq I]
theorem slopeInterpolants_cross_identity6401
    (sigma : F →+* F) (alpha : I ↪ F)
    (hfixed : ∀ i, sigma (alpha i) = alpha i)
    (u : I → F) (A B L R : F[X])
    (hL : ∀ i, L.eval (alpha i) = A.eval (alpha i) * sigma (u i))
    (hR : ∀ i, R.eval (alpha i) = B.eval (alpha i) * u i)
    (hdegLeft : (L * B.map sigma).natDegree < Fintype.card I)
    (hdegRight : (A * R.map sigma).natDegree < Fintype.card I) :
    L * B.map sigma = A * R.map sigma := by
  classical
  apply Polynomial.eq_of_natDegree_lt_card_of_eval_eq'
    (L * B.map sigma) (A * R.map sigma)
      ((Finset.univ : Finset I).map alpha)
  · intro x hx
    obtain ⟨i, _hi, rfl⟩ := Finset.mem_map.mp hx
    simp only [Polynomial.eval_mul]
    rw [eval_map_eq_map_eval_of_fixed sigma B (alpha i) (hfixed i),
      eval_map_eq_map_eval_of_fixed sigma R (alpha i) (hfixed i),
      hL i, hR i, map_mul]
    ring
  · rw [Finset.card_map, Finset.card_univ]
    exact max_lt hdegLeft hdegRight
theorem slopeInterpolants_factor_of_orbitCrossCoprime6401
    (sigma : F →+* F) (alpha : I ↪ F)
    (hfixed : ∀ i, sigma (alpha i) = alpha i)
    (u : I → F) (A B L R : F[X])
    (hA : A ≠ 0)
    (hcrossCoprime : IsCoprime A (B.map sigma))
    (hL : ∀ i, L.eval (alpha i) = A.eval (alpha i) * sigma (u i))
    (hR : ∀ i, R.eval (alpha i) = B.eval (alpha i) * u i)
    (hdegLeft : (L * B.map sigma).natDegree < Fintype.card I)
    (hdegRight : (A * R.map sigma).natDegree < Fintype.card I) :
    ∃ W : F[X], L = A * W ∧
      R.map sigma = B.map sigma * W := by
  have hcross := slopeInterpolants_cross_identity6401
    sigma alpha hfixed u A B L R hL hR hdegLeft hdegRight
  have hdvdProduct : A ∣ L * B.map sigma :=
    ⟨R.map sigma, hcross⟩
  obtain ⟨W, hLW⟩ := hcrossCoprime.dvd_of_dvd_mul_right hdvdProduct
  refine ⟨W, hLW, ?_⟩
  apply mul_left_cancel₀ hA
  calc
    A * R.map sigma = L * B.map sigma := hcross.symm
    _ = (A * W) * B.map sigma := by rw [hLW]
    _ = A * (B.map sigma * W) := by ring
theorem slopeInterpolants_commonFactor_of_orbitCrossCoprime6401
    (sigma : F →+* F)
    (horder : ∀ x : F,
      sigma (sigma (sigma (sigma (sigma (sigma x))))) = x)
    (alpha : I ↪ F) (hfixed : ∀ i, sigma (alpha i) = alpha i)
    (u : I → F) (A B L R : F[X])
    (hA : A ≠ 0)
    (hcrossCoprime : IsCoprime A (B.map sigma))
    (hL : ∀ i, L.eval (alpha i) = A.eval (alpha i) * sigma (u i))
    (hR : ∀ i, R.eval (alpha i) = B.eval (alpha i) * u i)
    (hdegLeft : (L * B.map sigma).natDegree < Fintype.card I)
    (hdegRight : (A * R.map sigma).natDegree < Fintype.card I) :
    ∃ V : F[X], L = A * V.map sigma ∧ R = B * V := by
  obtain ⟨W, hLW, hRW⟩ :=
    slopeInterpolants_factor_of_orbitCrossCoprime6401
      sigma alpha hfixed u A B L R hA hcrossCoprime
        hL hR hdegLeft hdegRight
  let V : F[X] :=
    (((((W.map sigma).map sigma).map sigma).map sigma).map sigma)
  have hVmap : V.map sigma = W := by
    exact polynomial_map_six_eq_self6401 sigma horder W
  refine ⟨V, ?_, ?_⟩
  · simpa [hVmap] using hLW
  · apply Polynomial.map_injective sigma sigma.injective
    rw [Polynomial.map_mul, hVmap]
    exact hRW
end CorrectedSlopeDescent
section AdjacentOrbitCounterprofile
variable {F I : Type*} [Field F] [Fintype I] [DecidableEq I]
theorem adjacentOrbit_slopeDescent_counterprofile6401
    (sigma : F →+* F)
    (horder : ∀ x : F,
      sigma (sigma (sigma (sigma (sigma (sigma x))))) = x)
    (beta : F) (hmove : beta ≠ sigma beta)
    (alpha : I ↪ F) (hfixed : ∀ i, sigma (alpha i) = alpha i)
    (hcard : 2 ≤ Fintype.card I) :
    let B := linearFactor beta
    let A := linearFactor (sigma beta)
    let L : F[X] := 1
    let R : F[X] := 1
    let u : I → F := fun i ↦ (B.eval (alpha i))⁻¹
    A ≠ 0 ∧ B ≠ 0 ∧ IsCoprime A B ∧
      polynomialFrobeniusNormSix sigma A =
        polynomialFrobeniusNormSix sigma B ∧
      B.map sigma = A ∧
      ¬ IsCoprime A (B.map sigma) ∧
      (L * B.map sigma).natDegree < Fintype.card I ∧
      (A * R.map sigma).natDegree < Fintype.card I ∧
      (∀ i, L.eval (alpha i) = A.eval (alpha i) * sigma (u i)) ∧
      (∀ i, R.eval (alpha i) = B.eval (alpha i) * u i) ∧
      L * B.map sigma = A * R.map sigma ∧
      ¬ ∃ V : F[X], L = A * V.map sigma ∧ R = B * V := by
  classical
  dsimp only
  have hA : linearFactor (sigma beta) ≠ 0 :=
    Polynomial.X_sub_C_ne_zero (sigma beta)
  have hB : linearFactor beta ≠ 0 :=
    Polynomial.X_sub_C_ne_zero beta
  have hcop : IsCoprime (linearFactor (sigma beta))
      (linearFactor beta) :=
    (linearFactor_isCoprime_conjugate sigma beta hmove).symm
  have hmap : (linearFactor beta).map sigma =
      linearFactor (sigma beta) := linearFactor_map sigma beta
  have hnorm : polynomialFrobeniusNormSix sigma
        (linearFactor (sigma beta)) =
      polynomialFrobeniusNormSix sigma (linearFactor beta) := by
    rw [← hmap]
    exact polynomialFrobeniusNormSix_map_eq6401 sigma horder
      (linearFactor beta)
  have hnotCross : ¬ IsCoprime (linearFactor (sigma beta))
      ((linearFactor beta).map sigma) := by
    rw [hmap]
    intro hself
    have hunit : IsUnit (linearFactor (sigma beta)) :=
      isCoprime_self.mp hself
    exact Polynomial.not_isUnit_of_natDegree_pos
      (linearFactor (sigma beta)) (by simp [linearFactor]) hunit
  have hleftDegree :
      ((1 : F[X]) * (linearFactor beta).map sigma).natDegree <
        Fintype.card I := by
    rw [hmap]
    simp only [one_mul]
    have hdegree : (linearFactor (sigma beta)).natDegree = 1 := by
      simp [linearFactor]
    omega
  have hrightDegree :
      (linearFactor (sigma beta) * (1 : F[X]).map sigma).natDegree <
        Fintype.card I := by
    simp only [Polynomial.map_one, mul_one]
    have hdegree : (linearFactor (sigma beta)).natDegree = 1 := by
      simp [linearFactor]
    omega
  have hLeval : ∀ i,
      (1 : F[X]).eval (alpha i) =
        (linearFactor (sigma beta)).eval (alpha i) *
          sigma (((linearFactor beta).eval (alpha i))⁻¹) := by
    intro i
    have hroot : alpha i ≠ beta :=
      fixed_locator_ne_moving_root sigma beta (alpha i) hmove (hfixed i)
    have hBne : (linearFactor beta).eval (alpha i) ≠ 0 := by
      simpa using sub_ne_zero.mpr hroot
    have heval := eval_map_eq_map_eval_of_fixed sigma
      (linearFactor beta) (alpha i) (hfixed i)
    rw [hmap] at heval
    have hAne : (linearFactor (sigma beta)).eval (alpha i) ≠ 0 := by
      rw [heval]
      exact (map_ne_zero_iff sigma sigma.injective).2 hBne
    simp only [Polynomial.eval_one]
    rw [map_inv₀, ← heval]
    exact (mul_inv_cancel₀ hAne).symm
  have hReval : ∀ i,
      (1 : F[X]).eval (alpha i) =
        (linearFactor beta).eval (alpha i) *
          ((linearFactor beta).eval (alpha i))⁻¹ := by
    intro i
    have hroot : alpha i ≠ beta :=
      fixed_locator_ne_moving_root sigma beta (alpha i) hmove (hfixed i)
    have hBne : (linearFactor beta).eval (alpha i) ≠ 0 := by
      simpa using sub_ne_zero.mpr hroot
    simpa using (mul_inv_cancel₀ hBne).symm
  have hcross :
      (1 : F[X]) * (linearFactor beta).map sigma =
        linearFactor (sigma beta) * (1 : F[X]).map sigma := by
    simp [hmap]
  have hnofactor : ¬ ∃ V : F[X],
      (1 : F[X]) = linearFactor (sigma beta) * V.map sigma ∧
        (1 : F[X]) = linearFactor beta * V := by
    rintro ⟨V, _hfirst, hsecond⟩
    have heval := congrArg (Polynomial.eval beta) hsecond
    simpa [linearFactor] using heval
  exact ⟨hA, hB, hcop, hnorm, hmap, hnotCross,
    hleftDegree, hrightDegree, hLeval, hReval, hcross, hnofactor⟩
end AdjacentOrbitCounterprofile
end BCHKSExtremePrimitiveFixedPairSlopeDescentNoGo6401
end ProximityPrize.SubmissionLower
