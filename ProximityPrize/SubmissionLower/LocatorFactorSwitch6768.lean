import ProximityPrize.SubmissionLower.LocatorLowQuotient

namespace ProximityPrize.SubmissionLower.LocatorFactorSwitch6768

open scoped BigOperators
open RCN081 RCN100 RCN119 RCN130 RCN156 RCN180 RCN234
open LocatorLowQuotient

noncomputable section

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

variable {K V : Type*} [Field K]
variable [AddCommGroup V] [Module K V]

local instance : DecidableEq K := Classical.decEq K

/-- Add the intermediate `Y+R` support cap to an ordinary flag box. -/
theorem mem_nested_of_global_and_ys
    (P : MvPolynomial (Fin 4) K) (D w T YS S : Nat)
    (hP : P ∈ globalCoefficientBox K D w T S)
    (hYS : wt residualYSWeights P ≤ YS) :
    P ∈ nestedCoefficientBox K D w T YS S := by
  intro d hd
  have hmiddle := MvPolynomial.le_weightedTotalDegree residualYSWeights hd
  rw [weight_fin4] at hmiddle
  simp only [residualYSWeights, Fin.isValue, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val, Nat.mul_zero, Nat.mul_one,
    Nat.zero_add, Nat.add_zero] at hmiddle
  have hmiddle' : d 1 + d 2 ≤ YS := by
    exact hmiddle.trans hYS
  exact ⟨(hP hd).1, hmiddle', (hP hd).2.1, (hP hd).2.2⟩

/-- Dividing a polynomial in a nested flag box subtracts all four lower
bounds carried by the divisor.  This is the factor-aware version of the
ordinary quotient-box lemma: it retains the intermediate `Y+R` cap. -/
theorem quotient_mem_nested_of_mul_eq
    (P F Q : MvPolynomial (Fin 4) K)
    (D w T YS S c t y s : Nat)
    (hP : P ∈ nestedCoefficientBox K D w T YS S)
    (hF : F ≠ 0) (hQ : Q ≠ 0) (heq : P = F * Q)
    (hc : c ≤ wt (contactWeights w) F)
    (ht : t ≤ wt residualTotalWeights F)
    (hy : y ≤ wt residualYSWeights F)
    (hs : s ≤ wt residualSWeights F) :
    Q ∈ nestedCoefficientBox K (D - c) w (T - t) (YS - y) (S - s) := by
  have hPne : P ≠ 0 := by
    rw [heq]
    exact mul_ne_zero hF hQ
  have hcaps := nested_mem_weights hP hPne
  have hcontact := weightedTotalDegree_mul (contactWeights w) F Q hF hQ
  have htotal := weightedTotalDegree_mul residualTotalWeights F Q hF hQ
  have hmiddle := weightedTotalDegree_mul residualYSWeights F Q hF hQ
  have hslope := weightedTotalDegree_mul residualSWeights F Q hF hQ
  rw [← heq] at hcontact htotal hmiddle hslope
  intro d hd
  have hdcontact := MvPolynomial.le_weightedTotalDegree (contactWeights w) hd
  have hdtotal := MvPolynomial.le_weightedTotalDegree residualTotalWeights hd
  have hdmiddle := MvPolynomial.le_weightedTotalDegree residualYSWeights hd
  have hdslope := MvPolynomial.le_weightedTotalDegree residualSWeights hd
  simp only [wt] at hc ht hy hs hcaps hcontact htotal hmiddle hslope
  have hQT : wt residualTotalWeights Q ≤ T - t := by
    simp only [wt]
    omega
  have hQY : wt residualYSWeights Q ≤ YS - y := by
    simp only [wt]
    omega
  have hQS : wt residualSWeights Q ≤ S - s := by
    simp only [wt]
    omega
  have hQC : wt (contactWeights w) Q < D - c := by
    simp only [wt]
    omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h := hdtotal.trans hQT
    rw [weight_fin4] at h
    simpa [residualTotalWeights] using h
  · have h := hdmiddle.trans hQY
    rw [weight_fin4] at h
    simpa [residualYSWeights] using h
  · have h := hdslope.trans hQS
    rw [weight_fin4] at h
    simpa [residualSWeights] using h
  · have h := hdcontact.trans_lt hQC
    rw [weight_fin4] at h
    simpa [contactWeights, Nat.mul_comm] using h

/-- The exact switch used at the 67.68 equality slice.

First kill one high contact band in the quotient image.  If that slice
contains a quotient not divisible by `F`, it is already the coprime arm.  If
the whole slice is divisible by `F`, divide the entire slice linearly by `F`
and kill a second high band in the much smaller cofactor box.  Thus the
second cut is charged against the cofactor channels, not against the original
large quotient box. -/
theorem exists_coprime_or_twice_low
    [FiniteDimensional K V]
    (Dhigh Dlow w delta T YS S c t y s delta₂ : Nat)
    (q : V →ₗ[K] MvPolynomial (Fin 4) K)
    (hq : Function.Injective q)
    (hmem : ∀ v, q v ∈ nestedCoefficientBox K Dhigh w T YS S)
    (F : MvPolynomial (Fin 4) K) (hF : F ≠ 0)
    (hc : c ≤ wt (contactWeights w) F)
    (ht : t ≤ wt residualTotalWeights F)
    (hy : y ≤ wt residualYSWeights F)
    (hs : s ≤ wt residualSWeights F)
    (hwidth : Dhigh ≤ Dlow + delta)
    (hwidth₂ : Dlow - c ≤ (Dlow - c - delta₂) + delta₂)
    (hsource :
      delta * channelCount T YS S +
          delta₂ * channelCount (T - t) (YS - y) (S - s) <
        Module.finrank K V) :
    ∃ v : V, v ≠ 0 ∧ q v ≠ 0 ∧
      ((q v ∈ nestedCoefficientBox K Dlow w T YS S ∧ ¬ F ∣ q v) ∨
        ∃ C : MvPolynomial (Fin 4) K,
          C ≠ 0 ∧ q v = F * C ∧
            C ∈ nestedCoefficientBox K (Dlow - c - delta₂) w
              (T - t) (YS - y) (S - s)) := by
  classical
  let band := (highBandMap (K := K) w Dlow delta T YS S).comp q
  let U : Submodule K V := LinearMap.ker band
  have hrange : Module.finrank K band.range ≤ delta * channelCount T YS S := by
    calc
      Module.finrank K band.range ≤
          Module.finrank K (HighBandIndex delta T YS S → K) := band.range.finrank_le
      _ = Fintype.card (HighBandIndex delta T YS S) :=
        Module.finrank_fintype_fun_eq_card K
      _ = delta * channelCount T YS S := highBandIndex_card delta T YS S
  have hsum := band.finrank_range_add_finrank_ker
  have hsecond :
      delta₂ * channelCount (T - t) (YS - y) (S - s) < Module.finrank K U := by
    dsimp only [U]
    omega
  have hlow (u : U) : q u.1 ∈ nestedCoefficientBox K Dlow w T YS S := by
    apply mem_low_of_highBandMap_eq_zero Dhigh Dlow w delta T YS S hwidth
      (q u.1) (hmem u.1)
    exact u.2
  by_cases hescape : ∃ u : U, ¬ F ∣ q u.1
  · obtain ⟨u, hu⟩ := hescape
    have hu0 : u.1 ≠ 0 := by
      intro hz
      apply hu
      rw [hz, map_zero]
      exact dvd_zero F
    have hqu : q u.1 ≠ 0 := by
      intro hz
      exact hu (hz ▸ dvd_zero F)
    exact ⟨u.1, hu0, hqu, Or.inl ⟨hlow u, hu⟩⟩
  · have hdiv : ∀ u : U, F ∣ q u.1 := by
      intro u
      by_contra hu
      exact hescape ⟨u, hu⟩
    let qU : U →ₗ[K] MvPolynomial (Fin 4) K := q.comp U.subtype
    let qC : U →ₗ[K] MvPolynomial (Fin 4) K := quotientLinear qU F hF hdiv
    have hqU : Function.Injective qU := by
      intro u v huv
      apply Subtype.ext
      exact hq huv
    have hqC : Function.Injective qC :=
      quotientLinear_injective qU hqU F hF hdiv
    have hCmem : ∀ u : U,
        qC u ∈ nestedCoefficientBox K (Dlow - c) w
          (T - t) (YS - y) (S - s) := by
      intro u
      by_cases hu : u = 0
      · subst u
        rw [map_zero]
        exact (nestedCoefficientBox K (Dlow - c) w
          (T - t) (YS - y) (S - s)).zero_mem
      · have hqu : qU u ≠ 0 := by
          intro hz
          apply hu
          exact hqU (by simpa only [map_zero] using hz)
        have hCu : qC u ≠ 0 := by
          intro hz
          apply hu
          apply hqC
          simpa only [map_zero] using hz
        apply quotient_mem_nested_of_mul_eq (qU u) F (qC u)
          Dlow w T YS S c t y s (hlow u) hF hCu
        · exact recon_eq_mul_quotientPolynomial qU F hdiv u
        · exact hc
        · exact ht
        · exact hy
        · exact hs
    obtain ⟨u, hu, hCu, hClow⟩ := exists_nonzero_image_mem_low
      (Dlow - c) (Dlow - c - delta₂) w delta₂
      (T - t) (YS - y) (S - s) hwidth₂ qC hqC hCmem hsecond
    have hu0 : u.1 ≠ 0 := by
      intro hz
      apply hu
      apply Subtype.ext
      exact hz
    have hqu : q u.1 ≠ 0 := by
      intro hz
      exact hu0 (hq (by simpa only [map_zero] using hz))
    refine ⟨u.1, hu0, hqu, Or.inr ⟨qC u, hCu, ?_, hClow⟩⟩
    exact recon_eq_mul_quotientPolynomial qU F hdiv u

/-- Flexible form of the switch.  If the second band has enough room, use
`exists_coprime_or_twice_low`.  Otherwise the failed width inequality says
that the whole cofactor contact box is narrower than `delta`; a dimension
comparison then forces the first low slice to contain a quotient not
divisible by `F`. -/
theorem exists_coprime_or_twice_low_flexible
    [FiniteDimensional K V]
    (Dhigh Dlow w delta T YS S c t y s : Nat)
    (q : V →ₗ[K] MvPolynomial (Fin 4) K)
    (hq : Function.Injective q)
    (hmem : ∀ v, q v ∈ nestedCoefficientBox K Dhigh w T YS S)
    (F : MvPolynomial (Fin 4) K) (hF : F ≠ 0)
    (hc : c ≤ wt (contactWeights w) F)
    (ht : t ≤ wt residualTotalWeights F)
    (hy : y ≤ wt residualYSWeights F)
    (hs : s ≤ wt residualSWeights F)
    (hwidth : Dhigh ≤ Dlow + delta)
    (hsourceBands :
      delta * channelCount T YS S +
          delta * channelCount (T - t) (YS - y) (S - s) <
        Module.finrank K V)
    (hsourceSmall :
      delta * channelCount T YS S +
          coefficientCount delta w (T - t) (S - s) <
        Module.finrank K V) :
    ∃ v : V, v ≠ 0 ∧ q v ≠ 0 ∧
      ((q v ∈ nestedCoefficientBox K Dlow w T YS S ∧ ¬ F ∣ q v) ∨
        ∃ C : MvPolynomial (Fin 4) K,
          C ≠ 0 ∧ q v = F * C ∧
            C ∈ nestedCoefficientBox K (Dlow - c - delta) w
              (T - t) (YS - y) (S - s)) := by
  classical
  by_cases hwidth₂ : Dlow - c ≤ (Dlow - c - delta) + delta
  · exact exists_coprime_or_twice_low Dhigh Dlow w delta T YS S c t y s delta
      q hq hmem F hF hc ht hy hs hwidth hwidth₂ hsourceBands
  · clear hsourceBands
    have hsmallD : Dlow - c < delta := by omega
    let band := (highBandMap (K := K) w Dlow delta T YS S).comp q
    let U : Submodule K V := LinearMap.ker band
    have hrange : Module.finrank K band.range ≤ delta * channelCount T YS S := by
      calc
        Module.finrank K band.range ≤
            Module.finrank K (HighBandIndex delta T YS S → K) := band.range.finrank_le
        _ = Fintype.card (HighBandIndex delta T YS S) :=
          Module.finrank_fintype_fun_eq_card K
        _ = delta * channelCount T YS S := highBandIndex_card delta T YS S
    have hsum := band.finrank_range_add_finrank_ker
    have hUlarge : coefficientCount delta w (T - t) (S - s) <
        Module.finrank K U := by
      dsimp only [U]
      omega
    have hlow (u : U) : q u.1 ∈ nestedCoefficientBox K Dlow w T YS S := by
      apply mem_low_of_highBandMap_eq_zero Dhigh Dlow w delta T YS S hwidth
        (q u.1) (hmem u.1)
      exact u.2
    by_contra hnone
    have hdiv : ∀ u : U, F ∣ q u.1 := by
      intro u
      by_contra hu
      apply hnone
      have hu0 : u.1 ≠ 0 := by
        intro hz
        apply hu
        rw [hz, map_zero]
        exact dvd_zero F
      have hqu : q u.1 ≠ 0 := by
        intro hz
        exact hu (hz ▸ dvd_zero F)
      exact ⟨u.1, hu0, hqu, Or.inl ⟨hlow u, hu⟩⟩
    let qU : U →ₗ[K] MvPolynomial (Fin 4) K := q.comp U.subtype
    have hqU : Function.Injective qU := by
      intro u v huv
      apply Subtype.ext
      exact hq huv
    have hCmem : ∀ u : U,
        quotientPolynomial qU F hdiv u ∈
          globalCoefficientBox K delta w (T - t) (S - s) := by
      intro u
      by_cases hu : u = 0
      · subst u
        have hz : quotientPolynomial qU F hdiv 0 = 0 :=
          (quotientLinear qU F hF hdiv).map_zero
        rw [hz]
        exact (globalCoefficientBox K delta w (T - t) (S - s)).zero_mem
      · have hqu : qU u ≠ 0 := by
          intro hz
          apply hu
          exact hqU (by simpa only [map_zero] using hz)
        have hCu : quotientPolynomial qU F hdiv u ≠ 0 := by
          intro hz
          apply hqu
          rw [recon_eq_mul_quotientPolynomial qU F hdiv u, hz, mul_zero]
        have hnested := quotient_mem_nested_of_mul_eq
          (qU u) F (quotientPolynomial qU F hdiv u)
          Dlow w T YS S c t y s (hlow u) hF hCu
          (recon_eq_mul_quotientPolynomial qU F hdiv u)
          hc ht hy hs
        intro d hd
        have h := hnested hd
        exact ⟨h.1, h.2.2.1, h.2.2.2.trans hsmallD⟩
    have hdim := finrank_le_quotient_box qU hqU F hF hdiv
      (globalCoefficientBox K delta w (T - t) (S - s)) hCmem
    rw [globalCoefficientBox_finrank] at hdim
    exact (Nat.not_lt_of_ge hdim) hUlarge

end

end ProximityPrize.SubmissionLower.LocatorFactorSwitch6768

#print axioms ProximityPrize.SubmissionLower.LocatorFactorSwitch6768.exists_coprime_or_twice_low
#print axioms ProximityPrize.SubmissionLower.LocatorFactorSwitch6768.exists_coprime_or_twice_low_flexible
