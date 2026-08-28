import ProximityPrize.SubmissionLower.ContactImplicitContactLift

namespace ProximityPrize.SubmissionLower.ContactJointSeedCaps

open ContactFactorCaps ContactTaylorNumerators ContactSingularDegreeBounds
open ContactImplicitContactLift

noncomputable section

variable {K : Type*} [Field K]

abbrev Poly4 (K : Type*) [Field K] := MvPolynomial (Fin 4) K

local notation:1000 "W " P:1000 => MvPolynomial.weightedTotalDegree seedWeights P

lemma wt_neg (P : Poly4 K) : W (-P) = W P := by
  rw [← degree_weightedLift, ← degree_weightedLift, map_neg, MvPolynomial.degreeOf_neg]

lemma wt_sub_le (P Q : Poly4 K) : W (P - Q) ≤ max (W P) (W Q) := by
  rw [sub_eq_add_neg]
  simpa only [wt_neg] using weighted_add_le seedWeights P (-Q)

lemma wt_pow_le (P : Poly4 K) (r : ℕ) : W (P ^ r) ≤ r * W P := by
  induction r with
  | zero =>
      rw [pow_zero, ← degree_weightedLift]
      simp
  | succ r ih =>
      rw [pow_succ]
      calc
        _ ≤ W (P ^ r) + W P := weighted_mul_le seedWeights (P ^ r) P
        _ ≤ r * W P + W P := Nat.add_le_add_right ih _
        _ = (r + 1) * W P := by ring

lemma wt_zero : W (0 : Poly4 K) = 0 := by
  rw [← degree_weightedLift]
  simp

lemma wt_sum_le {ι : Type*} [DecidableEq ι] (S : Finset ι) (f : ι → Poly4 K) (a : ℕ)
    (hf : ∀ i ∈ S, W (f i) ≤ a) : W (∑ i ∈ S, f i) ≤ a := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [wt_zero]
  | @insert i S hi ih =>
      rw [Finset.sum_insert hi]
      exact (weighted_add_le seedWeights _ _).trans
        (max_le (hf i (Finset.mem_insert_self i S))
          (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))))

lemma wt_C (a : K) : W (MvPolynomial.C a : Poly4 K) = 0 := by
  simp [MvPolynomial.weightedTotalDegree]

lemma wt_natCast (r : ℕ) : W (r : Poly4 K) = 0 := by
  rw [← map_natCast (MvPolynomial.C : K →+* Poly4 K) r, wt_C]

lemma wt_R : W (MvPolynomial.X (2 : Fin 4) : Poly4 K) = 0 := by
  rw [weighted_X]
  rfl

lemma polyH_wt_le (F : Poly4 K) : W (polyH K F) ≤ W F :=
  pderiv_weight_le seedWeights F 2

lemma polyG_wt_le (F : Poly4 K) : W (polyG K F) ≤ W F := by
  unfold polyG
  rw [wt_neg]
  refine (weighted_add_le seedWeights _ _).trans (max_le ?_ ?_)
  · exact pderiv_weight_le seedWeights F 0
  · have hm := weighted_mul_le seedWeights (MvPolynomial.X (2 : Fin 4))
      (MvPolynomial.pderiv (1 : Fin 4) F)
    rw [wt_R, zero_add] at hm
    exact hm.trans (pderiv_weight_le seedWeights F 1)

lemma numeratorStep_joint_wt_le
    (F M : Poly4 K) (r A L : ℕ) (hF : W F ≤ L) (hM : W M ≤ A) :
    W (numeratorStep K F r M) ≤ A + 2 * L := by
  let H := polyH K F
  let G := polyG K F
  let R : Poly4 K := MvPolynomial.X (2 : Fin 4)
  have hH : W H ≤ L := (polyH_wt_le F).trans hF
  have hG : W G ≤ L := (polyG_wt_le F).trans hF
  have hR : W R = 0 := wt_R
  have hH2 : W (H ^ 2) ≤ 2 * L := (wt_pow_le H 2).trans (Nat.mul_le_mul_left 2 hH)
  have hMX : W (MvPolynomial.pderiv (0 : Fin 4) M) ≤ A :=
    (pderiv_weight_le seedWeights M 0).trans hM
  have hMY : W (MvPolynomial.pderiv (1 : Fin 4) M) ≤ A :=
    (pderiv_weight_le seedWeights M 1).trans hM
  have hMR : W (MvPolynomial.pderiv (2 : Fin 4) M) ≤ A :=
    (pderiv_weight_le seedWeights M 2).trans hM
  have hHX : W (MvPolynomial.pderiv (0 : Fin 4) H) ≤ L :=
    (pderiv_weight_le seedWeights H 0).trans hH
  have hHY : W (MvPolynomial.pderiv (1 : Fin 4) H) ≤ L :=
    (pderiv_weight_le seedWeights H 1).trans hH
  have hHR : W (MvPolynomial.pderiv (2 : Fin 4) H) ≤ L :=
    (pderiv_weight_le seedWeights H 2).trans hH
  have h1 : W (H ^ 2 * MvPolynomial.pderiv (0 : Fin 4) M) ≤ A + 2 * L := by
    have hh := weighted_mul_le seedWeights (H ^ 2) (MvPolynomial.pderiv (0 : Fin 4) M)
    omega
  have h2 : W (R * H ^ 2 * MvPolynomial.pderiv (1 : Fin 4) M) ≤ A + 2 * L := by
    have hh1 := weighted_mul_le seedWeights R (H ^ 2)
    have hh2 := weighted_mul_le seedWeights (R * H ^ 2) (MvPolynomial.pderiv (1 : Fin 4) M)
    rw [hR, zero_add] at hh1
    omega
  have h3 : W (G * H * MvPolynomial.pderiv (2 : Fin 4) M) ≤ A + 2 * L := by
    have hh1 := weighted_mul_le seedWeights G H
    have hh2 := weighted_mul_le seedWeights (G * H) (MvPolynomial.pderiv (2 : Fin 4) M)
    omega
  have hbx : W (H * MvPolynomial.pderiv (0 : Fin 4) H) ≤ 2 * L := by
    have hh := weighted_mul_le seedWeights H (MvPolynomial.pderiv (0 : Fin 4) H)
    omega
  have hby : W (R * H * MvPolynomial.pderiv (1 : Fin 4) H) ≤ 2 * L := by
    have hh1 := weighted_mul_le seedWeights R H
    have hh2 := weighted_mul_le seedWeights (R * H) (MvPolynomial.pderiv (1 : Fin 4) H)
    rw [hR, zero_add] at hh1
    omega
  have hbr : W (G * MvPolynomial.pderiv (2 : Fin 4) H) ≤ 2 * L := by
    have hh := weighted_mul_le seedWeights G (MvPolynomial.pderiv (2 : Fin 4) H)
    omega
  have hbrace : W (H * MvPolynomial.pderiv (0 : Fin 4) H +
      R * H * MvPolynomial.pderiv (1 : Fin 4) H +
      G * MvPolynomial.pderiv (2 : Fin 4) H) ≤ 2 * L := by
    exact (weighted_add_le seedWeights _ _).trans
      (max_le ((weighted_add_le seedWeights _ _).trans (max_le hbx hby)) hbr)
  have hn : W ((2 * r : ℕ) : Poly4 K) = 0 := wt_natCast (2 * r)
  have hnM : W (((2 * r : ℕ) : Poly4 K) * M) ≤ A := by
    have hh := weighted_mul_le seedWeights (((2 * r : ℕ) : Poly4 K)) M
    rw [hn, zero_add] at hh
    exact hh.trans hM
  have h4 : W (((2 * r : ℕ) : Poly4 K) * M *
      (H * MvPolynomial.pderiv (0 : Fin 4) H +
        R * H * MvPolynomial.pderiv (1 : Fin 4) H +
        G * MvPolynomial.pderiv (2 : Fin 4) H)) ≤ A + 2 * L := by
    have hh := weighted_mul_le seedWeights (((2 * r : ℕ) : Poly4 K) * M)
      (H * MvPolynomial.pderiv (0 : Fin 4) H +
        R * H * MvPolynomial.pderiv (1 : Fin 4) H +
        G * MvPolynomial.pderiv (2 : Fin 4) H)
    omega
  change W (H ^ 2 * MvPolynomial.pderiv (0 : Fin 4) M +
      R * H ^ 2 * MvPolynomial.pderiv (1 : Fin 4) M +
      G * H * MvPolynomial.pderiv (2 : Fin 4) M -
      ((2 * r : ℕ) : Poly4 K) * M *
        (H * MvPolynomial.pderiv (0 : Fin 4) H +
          R * H * MvPolynomial.pderiv (1 : Fin 4) H +
          G * MvPolynomial.pderiv (2 : Fin 4) H)) ≤ A + 2 * L
  apply (wt_sub_le _ _).trans
  exact max_le
    ((weighted_add_le seedWeights _ _).trans
      (max_le ((weighted_add_le seedWeights _ _).trans (max_le h1 h2)) h3)) h4

lemma numerator_joint_wt_le (F : Poly4 K) (L : ℕ) (hF : W F ≤ L) (r : ℕ) :
    W (numerator K F r) ≤ 1 + 2 * r * L := by
  induction r with
  | zero =>
      simp only [numerator_zero, Nat.mul_zero, Nat.zero_mul, Nat.add_zero]
      rw [weighted_X]
      rfl
  | succ r ih =>
      rw [numerator_succ]
      have hh := numeratorStep_joint_wt_le F (numerator K F r) r
        (1 + 2 * r * L) L hF ih
      calc
        _ ≤ (1 + 2 * r * L) + 2 * L := hh
        _ = 1 + 2 * (r + 1) * L := by ring

lemma shiftedX_joint_wt_zero (x : K) :
    W (MvPolynomial.C x - MvPolynomial.X (0 : Fin 4) : Poly4 K) = 0 := by
  apply Nat.eq_zero_of_le_zero
  apply (wt_sub_le _ _).trans
  rw [wt_C, weighted_X]
  rfl

lemma commonNumeratorTerm_joint_wt_le
    (F : Poly4 K) (L w j : ℕ) (hj : j ≤ w) (hF : W F ≤ L)
    (c : ℕ → K) (x : K) :
    W (commonNumeratorTerm F w c x j) ≤ 1 + 2 * w * L := by
  have hM := numerator_joint_wt_le F L hF j
  have hC : W (MvPolynomial.C (c j) * numerator K F j) ≤ 1 + 2 * j * L := by
    have hh := weighted_mul_le seedWeights (MvPolynomial.C (c j)) (numerator K F j)
    rw [wt_C, zero_add] at hh
    exact hh.trans hM
  have hH := (polyH_wt_le F).trans hF
  have hHP := (wt_pow_le (polyH K F) (2 * (w - j))).trans
    (Nat.mul_le_mul_left (2 * (w - j)) hH)
  have hX := wt_pow_le (MvPolynomial.C x - MvPolynomial.X (0 : Fin 4) : Poly4 K) j
  rw [shiftedX_joint_wt_zero x, Nat.mul_zero] at hX
  have hh1 := weighted_mul_le seedWeights
    (MvPolynomial.C (c j) * numerator K F j) (polyH K F ^ (2 * (w - j)))
  have hh2 := weighted_mul_le seedWeights
    (MvPolynomial.C (c j) * numerator K F j * polyH K F ^ (2 * (w - j)))
    ((MvPolynomial.C x - MvPolynomial.X (0 : Fin 4)) ^ j)
  have hwj : j + (w - j) = w := by omega
  dsimp only [commonNumeratorTerm]
  calc
    _ ≤ W (MvPolynomial.C (c j) * numerator K F j * polyH K F ^ (2 * (w - j))) +
        W ((MvPolynomial.C x - MvPolynomial.X (0 : Fin 4)) ^ j) := hh2
    _ ≤ (1 + 2 * j * L + (2 * (w - j)) * L) + 0 := by omega
    _ = 1 + 2 * (j + (w - j)) * L := by ring
    _ = 1 + 2 * w * L := by rw [hwj]

lemma clearedTaylorNumerator_joint_wt_le
    (F : Poly4 K) (L w : ℕ) (hF : W F ≤ L) (c : ℕ → K) (x : K) :
    W (clearedTaylorNumerator F w c x) ≤ 1 + 2 * w * L := by
  unfold clearedTaylorNumerator
  apply wt_sum_le
  intro j hj
  exact commonNumeratorTerm_joint_wt_le F L w j
    (by have hh := Finset.mem_range.mp hj; omega) hF c x

lemma affineSeedPolynomial_joint_wt_le (u₀ u₁ : K) :
    W (affineSeedPolynomial u₀ u₁ : Poly4 K) ≤ 1 := by
  unfold affineSeedPolynomial
  apply (weighted_add_le seedWeights _ _).trans
  apply max_le
  · rw [wt_C]; omega
  · have hh := weighted_mul_le seedWeights (MvPolynomial.X (3 : Fin 4))
      (MvPolynomial.C u₁)
    rw [weighted_X, wt_C, Nat.add_zero] at hh
    exact hh

lemma agreementNumerator_joint_wt_le
    (F : Poly4 K) (L w : ℕ) (hF : W F ≤ L)
    (c : ℕ → K) (x u₀ u₁ : K) :
    W (agreementNumerator F w c x u₀ u₁) ≤ 1 + 2 * w * L := by
  unfold agreementNumerator
  apply (wt_sub_le _ _).trans
  apply max_le (clearedTaylorNumerator_joint_wt_le F L w hF c x)
  have hH := (polyH_wt_le F).trans hF
  have hHP := (wt_pow_le (polyH K F) (2 * w)).trans (Nat.mul_le_mul_left (2 * w) hH)
  have hh := weighted_mul_le seedWeights (affineSeedPolynomial u₀ u₁) (polyH K F ^ (2 * w))
  have ha := affineSeedPolynomial_joint_wt_le (K := K) u₀ u₁
  omega

end

end ProximityPrize.SubmissionLower.ContactJointSeedCaps

