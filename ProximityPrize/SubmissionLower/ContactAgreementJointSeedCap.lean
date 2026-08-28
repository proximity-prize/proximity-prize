import ProximityPrize.SubmissionLower.ContactImplicitContactLift

/-!
# Joint seed-support cap for the actual agreement numerator

The separated Y and Z caps are not enough for the sparse resultant ledger.
This file proves the sharper joint Y+Z cap directly through the actual
contact-Taylor recurrence, using `seedWeights = ![0,1,0,1]`.
-/

namespace ProximityPrize.SubmissionLower.ContactAgreementJointSeedCap

open ContactTaylorNumerators ContactFactorCaps ContactImplicitContactLift
open ContactSingularDegreeBounds
open ContactDifferentialRing

noncomputable section

variable {K : Type*} [Field K]

theorem weighted_neg_eq (weights : Fin 4 → ℕ) (P : Poly4 K) :
    MvPolynomial.weightedTotalDegree weights (-P) =
      MvPolynomial.weightedTotalDegree weights P := by
  rw [← degree_weightedLift, map_neg, MvPolynomial.degreeOf_neg,
    degree_weightedLift]

theorem weighted_sub_le (weights : Fin 4 → ℕ) (P Q : Poly4 K) :
    MvPolynomial.weightedTotalDegree weights (P - Q) ≤
      max (MvPolynomial.weightedTotalDegree weights P)
        (MvPolynomial.weightedTotalDegree weights Q) := by
  rw [sub_eq_add_neg]
  simpa only [weighted_neg_eq] using weighted_add_le weights P (-Q)

theorem weighted_pow_le (weights : Fin 4 → ℕ) (P : Poly4 K) (n : ℕ) :
    MvPolynomial.weightedTotalDegree weights (P ^ n) ≤
      n * MvPolynomial.weightedTotalDegree weights P := by
  rw [← degree_weightedLift, map_pow]
  simpa only [degree_weightedLift] using
    MvPolynomial.degreeOf_pow_le (4 : Fin 5) (weightedLift K weights P) n

theorem weighted_C_eq_zero (weights : Fin 4 → ℕ) (a : K) :
    MvPolynomial.weightedTotalDegree weights (MvPolynomial.C a : Poly4 K) = 0 := by
  classical
  apply Nat.eq_zero_of_le_zero
  apply (weightedTotalDegree_le_iff weights _ 0).mpr
  intro d hd
  have hz : d = 0 := Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset hd)
  subst d
  simp

theorem polyH_seed_weight_le (F : Poly4 K) :
    MvPolynomial.weightedTotalDegree seedWeights (polyH K F) ≤
      MvPolynomial.weightedTotalDegree seedWeights F :=
  pderiv_weight_le seedWeights F 2

theorem polyG_seed_weight_le (F : Poly4 K) :
    MvPolynomial.weightedTotalDegree seedWeights (polyG K F) ≤
      MvPolynomial.weightedTotalDegree seedWeights F := by
  unfold polyG
  rw [weighted_neg_eq]
  have hx := pderiv_weight_le seedWeights F 0
  have hy := pderiv_weight_le seedWeights F 1
  have hR : MvPolynomial.weightedTotalDegree seedWeights
      (MvPolynomial.X (2 : Fin 4) : Poly4 K) = 0 := by
    rw [weighted_X]
    simp [seedWeights]
  have hm := weighted_mul_le seedWeights
    (MvPolynomial.X (2 : Fin 4) : Poly4 K)
    (MvPolynomial.pderiv (1 : Fin 4) F)
  rw [hR, zero_add] at hm
  exact (weighted_add_le seedWeights _ _).trans (max_le hx (hm.trans hy))

theorem numeratorStep_seed_weight_bound
    (F M : Poly4 K) (b a c : ℕ)
    (hF : MvPolynomial.weightedTotalDegree seedWeights F ≤ c)
    (hM : MvPolynomial.weightedTotalDegree seedWeights M ≤ a) :
    MvPolynomial.weightedTotalDegree seedWeights (numeratorStep K F b M) ≤
      a + 2 * c := by
  let H := polyH K F
  let G := polyG K F
  let R : Poly4 K := MvPolynomial.X (2 : Fin 4)
  have hR : MvPolynomial.weightedTotalDegree seedWeights R = 0 := by
    simp [R, weighted_X, seedWeights]
  have hH : MvPolynomial.weightedTotalDegree seedWeights H ≤ c :=
    (polyH_seed_weight_le F).trans hF
  have hG : MvPolynomial.weightedTotalDegree seedWeights G ≤ c :=
    (polyG_seed_weight_le F).trans hF
  have hH2 := (weighted_pow_le seedWeights H 2).trans (Nat.mul_le_mul_left 2 hH)
  have hMX := (pderiv_weight_le seedWeights M 0).trans hM
  have hMY := (pderiv_weight_le seedWeights M 1).trans hM
  have hMR := (pderiv_weight_le seedWeights M 2).trans hM
  have hHX := (pderiv_weight_le seedWeights H 0).trans hH
  have hHY := (pderiv_weight_le seedWeights H 1).trans hH
  have hHR := (pderiv_weight_le seedWeights H 2).trans hH
  have h1 := weighted_mul_le seedWeights (H ^ 2) (MvPolynomial.pderiv (0 : Fin 4) M)
  have h2a := weighted_mul_le seedWeights R (H ^ 2)
  have h2 := weighted_mul_le seedWeights (R * H ^ 2) (MvPolynomial.pderiv (1 : Fin 4) M)
  have h3a := weighted_mul_le seedWeights G H
  have h3 := weighted_mul_le seedWeights (G * H) (MvPolynomial.pderiv (2 : Fin 4) M)
  have hbx := weighted_mul_le seedWeights H (MvPolynomial.pderiv (0 : Fin 4) H)
  have hbya := weighted_mul_le seedWeights R H
  have hby := weighted_mul_le seedWeights (R * H) (MvPolynomial.pderiv (1 : Fin 4) H)
  have hbr := weighted_mul_le seedWeights G (MvPolynomial.pderiv (2 : Fin 4) H)
  have hn : MvPolynomial.weightedTotalDegree seedWeights
      (((2 * b : ℕ) : Poly4 K)) = 0 := by
    rw [← map_natCast (MvPolynomial.C : K →+* Poly4 K)]
    simpa [Nat.cast_mul] using weighted_C_eq_zero seedWeights (2 * (b : K))
  have hnM := weighted_mul_le seedWeights (((2 * b : ℕ) : Poly4 K)) M
  have hbrace1 := weighted_add_le seedWeights
    (H * MvPolynomial.pderiv (0 : Fin 4) H)
    (R * H * MvPolynomial.pderiv (1 : Fin 4) H)
  have hbrace := weighted_add_le seedWeights
    (H * MvPolynomial.pderiv (0 : Fin 4) H +
      R * H * MvPolynomial.pderiv (1 : Fin 4) H)
    (G * MvPolynomial.pderiv (2 : Fin 4) H)
  have h4 := weighted_mul_le seedWeights
    (((2 * b : ℕ) : Poly4 K) * M)
    (H * MvPolynomial.pderiv (0 : Fin 4) H +
      R * H * MvPolynomial.pderiv (1 : Fin 4) H +
      G * MvPolynomial.pderiv (2 : Fin 4) H)
  have ha1 : MvPolynomial.weightedTotalDegree seedWeights
      (H ^ 2 * MvPolynomial.pderiv (0 : Fin 4) M) ≤ a + 2 * c := by omega
  have ha2 : MvPolynomial.weightedTotalDegree seedWeights
      (R * H ^ 2 * MvPolynomial.pderiv (1 : Fin 4) M) ≤ a + 2 * c := by omega
  have ha3 : MvPolynomial.weightedTotalDegree seedWeights
      (G * H * MvPolynomial.pderiv (2 : Fin 4) M) ≤ a + 2 * c := by omega
  have hbbx : MvPolynomial.weightedTotalDegree seedWeights
      (H * MvPolynomial.pderiv (0 : Fin 4) H) ≤ 2 * c := by omega
  have hbby : MvPolynomial.weightedTotalDegree seedWeights
      (R * H * MvPolynomial.pderiv (1 : Fin 4) H) ≤ 2 * c := by omega
  have hbbr : MvPolynomial.weightedTotalDegree seedWeights
      (G * MvPolynomial.pderiv (2 : Fin 4) H) ≤ 2 * c := by omega
  have hb : MvPolynomial.weightedTotalDegree seedWeights
      (H * MvPolynomial.pderiv (0 : Fin 4) H +
        R * H * MvPolynomial.pderiv (1 : Fin 4) H +
        G * MvPolynomial.pderiv (2 : Fin 4) H) ≤ 2 * c := by
    exact hbrace.trans (max_le (hbrace1.trans (max_le hbbx hbby)) hbbr)
  have hnMa : MvPolynomial.weightedTotalDegree seedWeights
      (((2 * b : ℕ) : Poly4 K) * M) ≤ a := by omega
  have ha4 : MvPolynomial.weightedTotalDegree seedWeights
      (((2 * b : ℕ) : Poly4 K) * M *
        (H * MvPolynomial.pderiv (0 : Fin 4) H +
          R * H * MvPolynomial.pderiv (1 : Fin 4) H +
          G * MvPolynomial.pderiv (2 : Fin 4) H)) ≤ a + 2 * c := by omega
  change MvPolynomial.weightedTotalDegree seedWeights
    (H ^ 2 * MvPolynomial.pderiv (0 : Fin 4) M +
      R * H ^ 2 * MvPolynomial.pderiv (1 : Fin 4) M +
      G * H * MvPolynomial.pderiv (2 : Fin 4) M -
      ((2 * b : ℕ) : Poly4 K) * M *
        (H * MvPolynomial.pderiv (0 : Fin 4) H +
          R * H * MvPolynomial.pderiv (1 : Fin 4) H +
          G * MvPolynomial.pderiv (2 : Fin 4) H)) ≤ a + 2 * c
  exact (weighted_sub_le seedWeights _ _).trans
    (max_le ((weighted_add_le seedWeights _ _).trans
      (max_le ((weighted_add_le seedWeights _ _).trans (max_le ha1 ha2)) ha3)) ha4)

theorem numerator_seed_weight_bound
    (F : Poly4 K) (L b : ℕ)
    (hF : MvPolynomial.weightedTotalDegree seedWeights F ≤ L) :
    MvPolynomial.weightedTotalDegree seedWeights (numerator K F b) ≤
      1 + 2 * b * L := by
  induction b with
  | zero =>
      rw [numerator_zero, weighted_X]
      simp [seedWeights]
  | succ b ih =>
      rw [numerator_succ]
      have hh := numeratorStep_seed_weight_bound F (numerator K F b) b
        (1 + 2 * b * L) L hF ih
      convert hh using 1 <;> ring

theorem shiftedX_seed_weight_eq_zero (x : K) :
    MvPolynomial.weightedTotalDegree seedWeights
      (MvPolynomial.C x - MvPolynomial.X (0 : Fin 4) : Poly4 K) = 0 := by
  apply Nat.eq_zero_of_le_zero
  apply (weighted_sub_le seedWeights _ _).trans
  rw [weighted_C_eq_zero, weighted_X]
  simp [seedWeights]

theorem commonNumeratorTerm_seed_weight_bound
    (F : Poly4 K) (L w j : ℕ) (hj : j ≤ w)
    (hF : MvPolynomial.weightedTotalDegree seedWeights F ≤ L)
    (c : ℕ → K) (x : K) :
    MvPolynomial.weightedTotalDegree seedWeights
      (commonNumeratorTerm F w c x j) ≤ 1 + 2 * w * L := by
  have hC := weighted_C_eq_zero seedWeights (c j)
  have hM := numerator_seed_weight_bound F L j hF
  have hH := (polyH_seed_weight_le F).trans hF
  have hHP := (weighted_pow_le seedWeights (polyH K F) (2 * (w - j))).trans
    (Nat.mul_le_mul_left (2 * (w - j)) hH)
  have hXP := (weighted_pow_le seedWeights
    (MvPolynomial.C x - MvPolynomial.X (0 : Fin 4) : Poly4 K) j)
  rw [shiftedX_seed_weight_eq_zero, Nat.mul_zero] at hXP
  have h1 := weighted_mul_le seedWeights (MvPolynomial.C (c j) : Poly4 K)
    (numerator K F j)
  have h2 := weighted_mul_le seedWeights
    (MvPolynomial.C (c j) * numerator K F j) (polyH K F ^ (2 * (w - j)))
  have h3 := weighted_mul_le seedWeights
    (MvPolynomial.C (c j) * numerator K F j * polyH K F ^ (2 * (w - j)))
    ((MvPolynomial.C x - MvPolynomial.X (0 : Fin 4) : Poly4 K) ^ j)
  unfold commonNumeratorTerm
  have hw : j + (w - j) = w := by omega
  have hsub : j + (w - j) - j = w - j := by omega
  calc
    _ ≤ (0 + (1 + 2 * j * L)) + (2 * (w - j)) * L + 0 := by omega
    _ = 1 + 2 * w * L := by rw [← hw, hsub]; ring

theorem agreementNumerator_seed_weight_bound
    (F : Poly4 K) (L w : ℕ)
    (hF : MvPolynomial.weightedTotalDegree seedWeights F ≤ L)
    (c : ℕ → K) (x u₀ u₁ : K) :
    MvPolynomial.weightedTotalDegree seedWeights
      (agreementNumerator F w c x u₀ u₁) ≤ 2 * w * L + 1 := by
  have hsum : MvPolynomial.weightedTotalDegree seedWeights
      (clearedTaylorNumerator F w c x) ≤ 1 + 2 * w * L := by
    unfold clearedTaylorNumerator
    rw [← degree_weightedLift, map_sum]
    apply (MvPolynomial.degreeOf_sum_le (4 : Fin 5) _ _).trans
    apply Finset.sup_le
    intro j hj
    rw [degree_weightedLift]
    exact commonNumeratorTerm_seed_weight_bound F L w j
      (by have := Finset.mem_range.mp hj; omega) hF c x
  have haff : MvPolynomial.weightedTotalDegree seedWeights
      (affineSeedPolynomial u₀ u₁) ≤ 1 := by
    unfold affineSeedPolynomial
    have hC0 := weighted_C_eq_zero seedWeights u₀
    have hC1 := weighted_C_eq_zero seedWeights u₁
    have hZ : MvPolynomial.weightedTotalDegree seedWeights
        (MvPolynomial.X (3 : Fin 4) : Poly4 K) = 1 := by
      rw [weighted_X]
      simp [seedWeights]
    have hm := weighted_mul_le seedWeights
      (MvPolynomial.X (3 : Fin 4) : Poly4 K) (MvPolynomial.C u₁)
    exact (weighted_add_le seedWeights _ _).trans (by omega)
  have hH := (polyH_seed_weight_le F).trans hF
  have hHP := (weighted_pow_le seedWeights (polyH K F) (2 * w)).trans
    (Nat.mul_le_mul_left (2 * w) hH)
  have hprod := weighted_mul_le seedWeights (affineSeedPolynomial u₀ u₁)
    (polyH K F ^ (2 * w))
  unfold agreementNumerator
  apply (weighted_sub_le seedWeights _ _).trans
  apply max_le
  · omega
  · omega

theorem agreementNumerator_joint_seed_support_cap
    (F : Poly4 K) (L w : ℕ)
    (hF : MvPolynomial.weightedTotalDegree seedWeights F ≤ L)
    (c : ℕ → K) (x u₀ u₁ : K) :
    ∀ d ∈ (agreementNumerator F w c x u₀ u₁).support,
      d 1 + d 3 ≤ 2 * w * L + 1 := by
  intro d hd
  have hh := (MvPolynomial.le_weightedTotalDegree seedWeights hd).trans
    (agreementNumerator_seed_weight_bound F L w hF c x u₀ u₁)
  simpa only [seed_weight] using hh

end

end ProximityPrize.SubmissionLower.ContactAgreementJointSeedCap

#print axioms ProximityPrize.SubmissionLower.ContactAgreementJointSeedCap.agreementNumerator_seed_weight_bound
#print axioms ProximityPrize.SubmissionLower.ContactAgreementJointSeedCap.agreementNumerator_joint_seed_support_cap
