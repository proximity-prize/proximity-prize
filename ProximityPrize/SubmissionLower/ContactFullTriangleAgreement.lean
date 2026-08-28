import ProximityPrize.SubmissionLower.ContactJointSeedCaps
import ProximityPrize.SubmissionLower.ContactImplicitContactLift

/-!
# Full-triangle agreement cap

The reconstructed contact interpolant has the stronger support
`Y + R + Z ≤ L`. Giving all three surface variables weight one makes
`H = ∂R F` save one full unit. The Taylor recurrence therefore costs
`2 * (L - 1)` per step, improving the agreement seed-pair cap from
`1 + 2 * w * L` to `1 + 2 * w * (L - 1)`.
-/

namespace ProximityPrize.SubmissionLower.ContactFullTriangleAgreement

open ContactInterpolation ContactFactorCaps ContactTaylorNumerators
open ContactImplicitContactLift ContactJointSeedCaps ContactGenericSurface

noncomputable section

variable {K Ω : Type*} [Field K] [Field Ω]

def fullSurfaceWeights : Fin 4 → ℕ := ![0, 1, 1, 1]

local notation:1000 "WF " P:1000 =>
  MvPolynomial.weightedTotalDegree fullSurfaceWeights P

theorem full_surface_weight (d : Fin 4 →₀ ℕ) :
    Finsupp.weight fullSurfaceWeights d = d 1 + d 2 + d 3 := by
  rw [weight_fin4]
  simp [fullSurfaceWeights]

lemma fullTriangleBox_wt_le (F : MvPolynomial (Fin 4) K) (L : ℕ)
    (hF : F ∈ fullTriangleBox K L) : WF F ≤ L := by
  apply (weightedTotalDegree_le_iff fullSurfaceWeights F L).mpr
  intro d hd
  have ht : d 1 + d 2 + d 3 ≤ L := hF hd
  simpa only [full_surface_weight] using ht

lemma full_wt_le_of_dvd (F Q : MvPolynomial (Fin 4) K) (L : ℕ)
    (hQ : Q ≠ 0) (hdiv : F ∣ Q) (hfull : Q ∈ fullTriangleBox K L) :
    WF F ≤ L :=
  (weightedTotalDegree_le_of_dvd fullSurfaceWeights F Q hdiv hQ).trans
    (fullTriangleBox_wt_le Q L hfull)

lemma wf_neg (F : MvPolynomial (Fin 4) K) : WF (-F) = WF F := by
  rw [← degree_weightedLift, ← degree_weightedLift, map_neg,
    MvPolynomial.degreeOf_neg]

lemma wf_sub_le (F G : MvPolynomial (Fin 4) K) :
    WF (F - G) ≤ max (WF F) (WF G) := by
  rw [sub_eq_add_neg]
  simpa only [wf_neg] using weighted_add_le fullSurfaceWeights F (-G)

lemma wf_pow_le (F : MvPolynomial (Fin 4) K) (r : ℕ) :
    WF (F ^ r) ≤ r * WF F := by
  induction r with
  | zero =>
      rw [pow_zero, ← degree_weightedLift]
      simp
  | succ r ih =>
      rw [pow_succ]
      calc
        _ ≤ WF (F ^ r) + WF F := weighted_mul_le fullSurfaceWeights (F ^ r) F
        _ ≤ r * WF F + WF F := Nat.add_le_add_right ih _
        _ = (r + 1) * WF F := by ring

lemma wf_zero : WF (0 : MvPolynomial (Fin 4) K) = 0 := by
  rw [← degree_weightedLift]
  simp

lemma wf_sum_le {ι : Type*} [DecidableEq ι] (S : Finset ι)
    (f : ι → MvPolynomial (Fin 4) K) (a : ℕ)
    (hf : ∀ i ∈ S, WF (f i) ≤ a) : WF (∑ i ∈ S, f i) ≤ a := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [wf_zero]
  | @insert i S hi ih =>
      rw [Finset.sum_insert hi]
      exact (weighted_add_le fullSurfaceWeights _ _).trans
        (max_le (hf i (Finset.mem_insert_self i S))
          (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))))

lemma wf_C (a : K) : WF (MvPolynomial.C a : MvPolynomial (Fin 4) K) = 0 := by
  simp [MvPolynomial.weightedTotalDegree]

lemma wf_natCast (r : ℕ) : WF (r : MvPolynomial (Fin 4) K) = 0 := by
  rw [← map_natCast (MvPolynomial.C : K →+* MvPolynomial (Fin 4) K) r, wf_C]

lemma wf_X (i : Fin 4) :
    WF (MvPolynomial.X i : MvPolynomial (Fin 4) K) = fullSurfaceWeights i := by
  exact weighted_X fullSurfaceWeights i

lemma polyH_wf_le (F : MvPolynomial (Fin 4) K) (L : ℕ) (hL : WF F ≤ L) :
    WF (polyH K F) ≤ L - 1 := by
  exact pderiv_weight_sub_bound fullSurfaceWeights F 2 L hL

lemma polyG_wf_le (F : MvPolynomial (Fin 4) K) (L : ℕ) (hLpos : 1 ≤ L)
    (hL : WF F ≤ L) : WF (polyG K F) ≤ L := by
  unfold polyG
  rw [wf_neg]
  refine (weighted_add_le fullSurfaceWeights _ _).trans (max_le ?_ ?_)
  · exact (pderiv_weight_sub_bound fullSurfaceWeights F 0 L hL).trans (by omega)
  · have hY := pderiv_weight_sub_bound fullSurfaceWeights F 1 L hL
    have hwY : fullSurfaceWeights (1 : Fin 4) = 1 := rfl
    rw [hwY] at hY
    have hm := weighted_mul_le fullSurfaceWeights (MvPolynomial.X (2 : Fin 4))
      (MvPolynomial.pderiv (1 : Fin 4) F)
    have hw : fullSurfaceWeights (2 : Fin 4) = 1 := rfl
    rw [wf_X, hw] at hm
    exact hm.trans (by omega)

lemma numeratorStep_full_wt_le
    (F M : MvPolynomial (Fin 4) K) (r A L : ℕ)
    (hA : 1 ≤ A) (hLpos : 2 ≤ L) (hF : WF F ≤ L) (hM : WF M ≤ A) :
    WF (numeratorStep K F r M) ≤ A + 2 * (L - 1) := by
  let H := polyH K F
  let G := polyG K F
  let R : MvPolynomial (Fin 4) K := MvPolynomial.X (2 : Fin 4)
  have hH : WF H ≤ L - 1 := polyH_wf_le F L hF
  have hG : WF G ≤ L := polyG_wf_le F L (by omega) hF
  have hR : WF R = 1 := by
    dsimp only [R]
    rw [wf_X]
    rfl
  have hH2 : WF (H ^ 2) ≤ 2 * (L - 1) :=
    (wf_pow_le H 2).trans (Nat.mul_le_mul_left 2 hH)
  have hMX : WF (MvPolynomial.pderiv (0 : Fin 4) M) ≤ A :=
    (pderiv_weight_sub_bound fullSurfaceWeights M 0 A hM).trans (by omega)
  have hMY : WF (MvPolynomial.pderiv (1 : Fin 4) M) ≤ A - 1 :=
    pderiv_weight_sub_bound fullSurfaceWeights M 1 A hM
  have hMR : WF (MvPolynomial.pderiv (2 : Fin 4) M) ≤ A - 1 :=
    pderiv_weight_sub_bound fullSurfaceWeights M 2 A hM
  have hHX : WF (MvPolynomial.pderiv (0 : Fin 4) H) ≤ L - 1 :=
    (pderiv_weight_sub_bound fullSurfaceWeights H 0 (L - 1) hH).trans (by omega)
  have hHY : WF (MvPolynomial.pderiv (1 : Fin 4) H) ≤ (L - 1) - 1 :=
    pderiv_weight_sub_bound fullSurfaceWeights H 1 (L - 1) hH
  have hHR : WF (MvPolynomial.pderiv (2 : Fin 4) H) ≤ (L - 1) - 1 :=
    pderiv_weight_sub_bound fullSurfaceWeights H 2 (L - 1) hH
  have h1 : WF (H ^ 2 * MvPolynomial.pderiv (0 : Fin 4) M) ≤
      A + 2 * (L - 1) := by
    have hh := weighted_mul_le fullSurfaceWeights (H ^ 2)
      (MvPolynomial.pderiv (0 : Fin 4) M)
    omega
  have h2 : WF (R * H ^ 2 * MvPolynomial.pderiv (1 : Fin 4) M) ≤
      A + 2 * (L - 1) := by
    have hh1 := weighted_mul_le fullSurfaceWeights R (H ^ 2)
    have hh2 := weighted_mul_le fullSurfaceWeights (R * H ^ 2)
      (MvPolynomial.pderiv (1 : Fin 4) M)
    omega
  have h3 : WF (G * H * MvPolynomial.pderiv (2 : Fin 4) M) ≤
      A + 2 * (L - 1) := by
    have hh1 := weighted_mul_le fullSurfaceWeights G H
    have hh2 := weighted_mul_le fullSurfaceWeights (G * H)
      (MvPolynomial.pderiv (2 : Fin 4) M)
    omega
  have hbx : WF (H * MvPolynomial.pderiv (0 : Fin 4) H) ≤ 2 * (L - 1) := by
    have hh := weighted_mul_le fullSurfaceWeights H
      (MvPolynomial.pderiv (0 : Fin 4) H)
    omega
  have hby : WF (R * H * MvPolynomial.pderiv (1 : Fin 4) H) ≤
      2 * (L - 1) := by
    have hh1 := weighted_mul_le fullSurfaceWeights R H
    have hh2 := weighted_mul_le fullSurfaceWeights (R * H)
      (MvPolynomial.pderiv (1 : Fin 4) H)
    omega
  have hbr : WF (G * MvPolynomial.pderiv (2 : Fin 4) H) ≤ 2 * (L - 1) := by
    have hh := weighted_mul_le fullSurfaceWeights G
      (MvPolynomial.pderiv (2 : Fin 4) H)
    omega
  have hbrace : WF (H * MvPolynomial.pderiv (0 : Fin 4) H +
      R * H * MvPolynomial.pderiv (1 : Fin 4) H +
      G * MvPolynomial.pderiv (2 : Fin 4) H) ≤ 2 * (L - 1) := by
    exact (weighted_add_le fullSurfaceWeights _ _).trans
      (max_le ((weighted_add_le fullSurfaceWeights _ _).trans (max_le hbx hby)) hbr)
  have hn : WF ((2 * r : ℕ) : MvPolynomial (Fin 4) K) = 0 := wf_natCast (2 * r)
  have hnM : WF (((2 * r : ℕ) : MvPolynomial (Fin 4) K) * M) ≤ A := by
    have hh := weighted_mul_le fullSurfaceWeights
      (((2 * r : ℕ) : MvPolynomial (Fin 4) K)) M
    rw [hn, zero_add] at hh
    exact hh.trans hM
  have h4 : WF (((2 * r : ℕ) : MvPolynomial (Fin 4) K) * M *
      (H * MvPolynomial.pderiv (0 : Fin 4) H +
        R * H * MvPolynomial.pderiv (1 : Fin 4) H +
        G * MvPolynomial.pderiv (2 : Fin 4) H)) ≤ A + 2 * (L - 1) := by
    have hh := weighted_mul_le fullSurfaceWeights
      (((2 * r : ℕ) : MvPolynomial (Fin 4) K) * M)
      (H * MvPolynomial.pderiv (0 : Fin 4) H +
        R * H * MvPolynomial.pderiv (1 : Fin 4) H +
        G * MvPolynomial.pderiv (2 : Fin 4) H)
    omega
  change WF (H ^ 2 * MvPolynomial.pderiv (0 : Fin 4) M +
      R * H ^ 2 * MvPolynomial.pderiv (1 : Fin 4) M +
      G * H * MvPolynomial.pderiv (2 : Fin 4) M -
      ((2 * r : ℕ) : MvPolynomial (Fin 4) K) * M *
        (H * MvPolynomial.pderiv (0 : Fin 4) H +
          R * H * MvPolynomial.pderiv (1 : Fin 4) H +
          G * MvPolynomial.pderiv (2 : Fin 4) H)) ≤ A + 2 * (L - 1)
  apply (wf_sub_le _ _).trans
  exact max_le
    ((weighted_add_le fullSurfaceWeights _ _).trans
      (max_le ((weighted_add_le fullSurfaceWeights _ _).trans (max_le h1 h2)) h3)) h4

lemma numerator_full_wt_le (F : MvPolynomial (Fin 4) K) (L : ℕ)
    (hLpos : 2 ≤ L) (hF : WF F ≤ L) (r : ℕ) :
    WF (numerator K F r) ≤ 1 + 2 * r * (L - 1) := by
  induction r with
  | zero =>
      simp only [numerator_zero, Nat.mul_zero, Nat.zero_mul, Nat.add_zero]
      rw [wf_X]
      rfl
  | succ r ih =>
      rw [numerator_succ]
      have hh := numeratorStep_full_wt_le F (numerator K F r) r
        (1 + 2 * r * (L - 1)) L (by omega) hLpos hF ih
      calc
        _ ≤ (1 + 2 * r * (L - 1)) + 2 * (L - 1) := hh
        _ = 1 + 2 * (r + 1) * (L - 1) := by ring

lemma shiftedX_full_wt_zero (x : K) :
    WF (MvPolynomial.C x - MvPolynomial.X (0 : Fin 4) :
      MvPolynomial (Fin 4) K) = 0 := by
  apply Nat.eq_zero_of_le_zero
  apply (wf_sub_le _ _).trans
  rw [wf_C, wf_X]
  rfl

lemma commonNumeratorTerm_full_wt_le
    (F : MvPolynomial (Fin 4) K) (L w j : ℕ) (hLpos : 2 ≤ L)
    (hj : j ≤ w) (hF : WF F ≤ L) (c : ℕ → K) (x : K) :
    WF (commonNumeratorTerm F w c x j) ≤ 1 + 2 * w * (L - 1) := by
  have hM := numerator_full_wt_le F L hLpos hF j
  have hC : WF (MvPolynomial.C (c j) * numerator K F j) ≤
      1 + 2 * j * (L - 1) := by
    have hh := weighted_mul_le fullSurfaceWeights (MvPolynomial.C (c j))
      (numerator K F j)
    rw [wf_C, zero_add] at hh
    exact hh.trans hM
  have hH := polyH_wf_le F L hF
  have hHP := (wf_pow_le (polyH K F) (2 * (w - j))).trans
    (Nat.mul_le_mul_left (2 * (w - j)) hH)
  have hX := wf_pow_le
    (MvPolynomial.C x - MvPolynomial.X (0 : Fin 4) : MvPolynomial (Fin 4) K) j
  rw [shiftedX_full_wt_zero x, Nat.mul_zero] at hX
  have hh1 := weighted_mul_le fullSurfaceWeights
    (MvPolynomial.C (c j) * numerator K F j) (polyH K F ^ (2 * (w - j)))
  have hh2 := weighted_mul_le fullSurfaceWeights
    (MvPolynomial.C (c j) * numerator K F j * polyH K F ^ (2 * (w - j)))
    ((MvPolynomial.C x - MvPolynomial.X (0 : Fin 4)) ^ j)
  have hwj : j + (w - j) = w := by omega
  dsimp only [commonNumeratorTerm]
  calc
    _ ≤ WF (MvPolynomial.C (c j) * numerator K F j *
        polyH K F ^ (2 * (w - j))) +
        WF ((MvPolynomial.C x - MvPolynomial.X (0 : Fin 4)) ^ j) := hh2
    _ ≤ (1 + 2 * j * (L - 1) + (2 * (w - j)) * (L - 1)) + 0 := by omega
    _ = 1 + 2 * (j + (w - j)) * (L - 1) := by ring
    _ = 1 + 2 * w * (L - 1) := by rw [hwj]

lemma clearedTaylorNumerator_full_wt_le
    (F : MvPolynomial (Fin 4) K) (L w : ℕ) (hLpos : 2 ≤ L)
    (hF : WF F ≤ L) (c : ℕ → K) (x : K) :
    WF (clearedTaylorNumerator F w c x) ≤ 1 + 2 * w * (L - 1) := by
  unfold clearedTaylorNumerator
  apply wf_sum_le
  intro j hj
  exact commonNumeratorTerm_full_wt_le F L w j hLpos
    (by have hh := Finset.mem_range.mp hj; omega) hF c x

lemma affineSeedPolynomial_full_wt_le (u₀ u₁ : K) :
    WF (affineSeedPolynomial u₀ u₁ : MvPolynomial (Fin 4) K) ≤ 1 := by
  unfold affineSeedPolynomial
  apply (weighted_add_le fullSurfaceWeights _ _).trans
  apply max_le
  · rw [wf_C]; omega
  · have hh := weighted_mul_le fullSurfaceWeights (MvPolynomial.X (3 : Fin 4))
      (MvPolynomial.C u₁)
    rw [wf_X, wf_C, Nat.add_zero] at hh
    exact hh

lemma agreementNumerator_full_wt_le
    (F : MvPolynomial (Fin 4) K) (L w : ℕ) (hLpos : 2 ≤ L)
    (hF : WF F ≤ L) (c : ℕ → K) (x u₀ u₁ : K) :
    WF (agreementNumerator F w c x u₀ u₁) ≤ 1 + 2 * w * (L - 1) := by
  unfold agreementNumerator
  apply (wf_sub_le _ _).trans
  apply max_le (clearedTaylorNumerator_full_wt_le F L w hLpos hF c x)
  have hH := polyH_wf_le F L hF
  have hHP := (wf_pow_le (polyH K F) (2 * w)).trans
    (Nat.mul_le_mul_left (2 * w) hH)
  have hh := weighted_mul_le fullSurfaceWeights (affineSeedPolynomial u₀ u₁)
    (polyH K F ^ (2 * w))
  have ha := affineSeedPolynomial_full_wt_le (K := K) u₀ u₁
  omega

lemma agreementNumerator_joint_seed_cap_full_triangle
    (F : MvPolynomial (Fin 4) K) (L w : ℕ) (hLpos : 2 ≤ L)
    (hF : WF F ≤ L) (c : ℕ → K) (x u₀ u₁ : K) :
    ∀ d ∈ (agreementNumerator F w c x u₀ u₁).support,
      d 1 + d 3 ≤ 1 + 2 * w * (L - 1) := by
  intro d hd
  have hdegree := (MvPolynomial.le_weightedTotalDegree fullSurfaceWeights hd).trans
    (agreementNumerator_full_wt_le F L w hLpos hF c x u₀ u₁)
  rw [full_surface_weight] at hdegree
  omega

theorem surface_agreement_joint_seed_cap_full_triangle
    (φ : Polynomial K →+* Ω) (F : MvPolynomial (Fin 4) K)
    (L w : ℕ) (hLpos : 2 ≤ L) (hF : WF F ≤ L)
    (c : ℕ → K) (x u₀ u₁ : K) :
    ∀ d ∈ (surfaceMap φ (agreementNumerator F w c x u₀ u₁)).support,
      d 0 + d 2 ≤ 1 + 2 * w * (L - 1) :=
  surfaceMap_joint_seed_cap φ _ _
    (agreementNumerator_joint_seed_cap_full_triangle F L w hLpos hF c x u₀ u₁)

theorem surface_agreement_seed_degree_cap_full_triangle
    (φ : Polynomial K →+* Ω) (F : MvPolynomial (Fin 4) K)
    (L w : ℕ) (hLpos : 2 ≤ L) (hF : WF F ≤ L)
    (c : ℕ → K) (x u₀ u₁ : K) :
    (surfaceMap φ (agreementNumerator F w c x u₀ u₁)).degreeOf 2 ≤
      1 + 2 * w * (L - 1) := by
  apply MvPolynomial.degreeOf_le_iff.mpr
  intro d hd
  have hj := surface_agreement_joint_seed_cap_full_triangle φ F L w hLpos hF
    c x u₀ u₁ d hd
  omega

end

end ProximityPrize.SubmissionLower.ContactFullTriangleAgreement

#print axioms ProximityPrize.SubmissionLower.ContactFullTriangleAgreement.fullTriangleBox_wt_le
#print axioms ProximityPrize.SubmissionLower.ContactFullTriangleAgreement.agreementNumerator_full_wt_le
#print axioms ProximityPrize.SubmissionLower.ContactFullTriangleAgreement.surface_agreement_joint_seed_cap_full_triangle
#print axioms ProximityPrize.SubmissionLower.ContactFullTriangleAgreement.surface_agreement_seed_degree_cap_full_triangle
