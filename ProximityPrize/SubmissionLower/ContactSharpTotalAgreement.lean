import ProximityPrize.SubmissionLower.ContactGenericSurface
import ProximityPrize.SubmissionLower.ContactFactorCaps
import ProximityPrize.SubmissionLower.ContactTaylorNumerators
import ProximityPrize.SubmissionLower.ContactImplicitContactLift

/-!
# Joint Y+R agreement cap

Giving Y and R weight one and X,Z weight zero makes every R derivative
lower this joint degree by one. For a factor of joint degree at most c,
the Taylor recurrence therefore costs 2*(c-1) per step.
-/

namespace ProximityPrize.SubmissionLower.ContactSharpTotalAgreement

open ContactInterpolation ContactFactorCaps ContactTaylorNumerators
open ContactImplicitContactLift ContactGenericSurface

noncomputable section

variable {K Ω : Type*} [Field K] [Field Ω]

def totalYRWeights : Fin 4 → ℕ := ![0, 1, 1, 0]

local notation:1000 "WF " P:1000 =>
  MvPolynomial.weightedTotalDegree totalYRWeights P

theorem totalYR_weight (d : Fin 4 →₀ ℕ) :
    Finsupp.weight totalYRWeights d = d 1 + d 2 := by
  rw [weight_fin4]
  simp [totalYRWeights]

lemma totalYR_wt_le_of_mem_box
    (F : MvPolynomial (Fin 4) K) (D w L s c : ℕ)
    (hw : 2 ≤ w) (hD : D ≤ (w - 1) * (c + 1))
    (hbox : F ∈ globalCoefficientBox K D w L s) :
    WF F ≤ c := by
  apply (weightedTotalDegree_le_iff totalYRWeights F c).mpr
  intro d hd
  have hc := (hbox hd).2.2
  have hmul : (w - 1) * (d 1 + d 2) ≤
      d 0 + w * d 1 + (w - 1) * d 2 := by
    have hy : (w - 1) * d 1 ≤ w * d 1 :=
      Nat.mul_le_mul_right (d 1) (Nat.sub_le w 1)
    calc
      (w - 1) * (d 1 + d 2) =
          (w - 1) * d 1 + (w - 1) * d 2 := by ring
      _ ≤ w * d 1 + (w - 1) * d 2 := Nat.add_le_add_right hy _
      _ ≤ d 0 + (w * d 1 + (w - 1) * d 2) := Nat.le_add_left _ _
      _ = d 0 + w * d 1 + (w - 1) * d 2 := by ring
  have hlt : (w - 1) * (d 1 + d 2) < (w - 1) * (c + 1) :=
    lt_of_le_of_lt hmul (hc.trans_le hD)
  have hsum : d 1 + d 2 < c + 1 :=
    (Nat.mul_lt_mul_left (by omega : 0 < w - 1)).mp hlt
  rw [totalYR_weight]
  omega

lemma wf_neg (F : MvPolynomial (Fin 4) K) : WF (-F) = WF F := by
  rw [← degree_weightedLift, ← degree_weightedLift, map_neg,
    MvPolynomial.degreeOf_neg]

lemma wf_sub_le (F G : MvPolynomial (Fin 4) K) :
    WF (F - G) ≤ max (WF F) (WF G) := by
  rw [sub_eq_add_neg]
  simpa only [wf_neg] using weighted_add_le totalYRWeights F (-G)

lemma wf_pow_le (F : MvPolynomial (Fin 4) K) (r : ℕ) :
    WF (F ^ r) ≤ r * WF F := by
  induction r with
  | zero =>
      rw [pow_zero, ← degree_weightedLift]
      simp
  | succ r ih =>
      rw [pow_succ]
      calc
        _ ≤ WF (F ^ r) + WF F := weighted_mul_le totalYRWeights (F ^ r) F
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
      exact (weighted_add_le totalYRWeights _ _).trans
        (max_le (hf i (Finset.mem_insert_self i S))
          (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))))

lemma wf_C (a : K) : WF (MvPolynomial.C a : MvPolynomial (Fin 4) K) = 0 := by
  simp [MvPolynomial.weightedTotalDegree]

lemma wf_natCast (r : ℕ) : WF (r : MvPolynomial (Fin 4) K) = 0 := by
  rw [← map_natCast (MvPolynomial.C : K →+* MvPolynomial (Fin 4) K) r, wf_C]

lemma wf_X (i : Fin 4) :
    WF (MvPolynomial.X i : MvPolynomial (Fin 4) K) = totalYRWeights i := by
  exact weighted_X totalYRWeights i

lemma polyH_wf_le (F : MvPolynomial (Fin 4) K) (L : ℕ) (hL : WF F ≤ L) :
    WF (polyH K F) ≤ L - 1 := by
  exact pderiv_weight_sub_bound totalYRWeights F 2 L hL

lemma polyG_wf_le (F : MvPolynomial (Fin 4) K) (L : ℕ) (hLpos : 1 ≤ L)
    (hL : WF F ≤ L) : WF (polyG K F) ≤ L := by
  unfold polyG
  rw [wf_neg]
  refine (weighted_add_le totalYRWeights _ _).trans (max_le ?_ ?_)
  · exact (pderiv_weight_sub_bound totalYRWeights F 0 L hL).trans (by omega)
  · have hY := pderiv_weight_sub_bound totalYRWeights F 1 L hL
    have hwY : totalYRWeights (1 : Fin 4) = 1 := rfl
    rw [hwY] at hY
    have hm := weighted_mul_le totalYRWeights (MvPolynomial.X (2 : Fin 4))
      (MvPolynomial.pderiv (1 : Fin 4) F)
    have hw : totalYRWeights (2 : Fin 4) = 1 := rfl
    rw [wf_X, hw] at hm
    exact hm.trans (by omega)

lemma numeratorStep_totalYR_wt_le
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
    (pderiv_weight_sub_bound totalYRWeights M 0 A hM).trans (by omega)
  have hMY : WF (MvPolynomial.pderiv (1 : Fin 4) M) ≤ A - 1 :=
    pderiv_weight_sub_bound totalYRWeights M 1 A hM
  have hMR : WF (MvPolynomial.pderiv (2 : Fin 4) M) ≤ A - 1 :=
    pderiv_weight_sub_bound totalYRWeights M 2 A hM
  have hHX : WF (MvPolynomial.pderiv (0 : Fin 4) H) ≤ L - 1 :=
    (pderiv_weight_sub_bound totalYRWeights H 0 (L - 1) hH).trans (by omega)
  have hHY : WF (MvPolynomial.pderiv (1 : Fin 4) H) ≤ (L - 1) - 1 :=
    pderiv_weight_sub_bound totalYRWeights H 1 (L - 1) hH
  have hHR : WF (MvPolynomial.pderiv (2 : Fin 4) H) ≤ (L - 1) - 1 :=
    pderiv_weight_sub_bound totalYRWeights H 2 (L - 1) hH
  have h1 : WF (H ^ 2 * MvPolynomial.pderiv (0 : Fin 4) M) ≤
      A + 2 * (L - 1) := by
    have hh := weighted_mul_le totalYRWeights (H ^ 2)
      (MvPolynomial.pderiv (0 : Fin 4) M)
    omega
  have h2 : WF (R * H ^ 2 * MvPolynomial.pderiv (1 : Fin 4) M) ≤
      A + 2 * (L - 1) := by
    have hh1 := weighted_mul_le totalYRWeights R (H ^ 2)
    have hh2 := weighted_mul_le totalYRWeights (R * H ^ 2)
      (MvPolynomial.pderiv (1 : Fin 4) M)
    omega
  have h3 : WF (G * H * MvPolynomial.pderiv (2 : Fin 4) M) ≤
      A + 2 * (L - 1) := by
    have hh1 := weighted_mul_le totalYRWeights G H
    have hh2 := weighted_mul_le totalYRWeights (G * H)
      (MvPolynomial.pderiv (2 : Fin 4) M)
    omega
  have hbx : WF (H * MvPolynomial.pderiv (0 : Fin 4) H) ≤ 2 * (L - 1) := by
    have hh := weighted_mul_le totalYRWeights H
      (MvPolynomial.pderiv (0 : Fin 4) H)
    omega
  have hby : WF (R * H * MvPolynomial.pderiv (1 : Fin 4) H) ≤
      2 * (L - 1) := by
    have hh1 := weighted_mul_le totalYRWeights R H
    have hh2 := weighted_mul_le totalYRWeights (R * H)
      (MvPolynomial.pderiv (1 : Fin 4) H)
    omega
  have hbr : WF (G * MvPolynomial.pderiv (2 : Fin 4) H) ≤ 2 * (L - 1) := by
    have hh := weighted_mul_le totalYRWeights G
      (MvPolynomial.pderiv (2 : Fin 4) H)
    omega
  have hbrace : WF (H * MvPolynomial.pderiv (0 : Fin 4) H +
      R * H * MvPolynomial.pderiv (1 : Fin 4) H +
      G * MvPolynomial.pderiv (2 : Fin 4) H) ≤ 2 * (L - 1) := by
    exact (weighted_add_le totalYRWeights _ _).trans
      (max_le ((weighted_add_le totalYRWeights _ _).trans (max_le hbx hby)) hbr)
  have hn : WF ((2 * r : ℕ) : MvPolynomial (Fin 4) K) = 0 := wf_natCast (2 * r)
  have hnM : WF (((2 * r : ℕ) : MvPolynomial (Fin 4) K) * M) ≤ A := by
    have hh := weighted_mul_le totalYRWeights
      (((2 * r : ℕ) : MvPolynomial (Fin 4) K)) M
    rw [hn, zero_add] at hh
    exact hh.trans hM
  have h4 : WF (((2 * r : ℕ) : MvPolynomial (Fin 4) K) * M *
      (H * MvPolynomial.pderiv (0 : Fin 4) H +
        R * H * MvPolynomial.pderiv (1 : Fin 4) H +
        G * MvPolynomial.pderiv (2 : Fin 4) H)) ≤ A + 2 * (L - 1) := by
    have hh := weighted_mul_le totalYRWeights
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
    ((weighted_add_le totalYRWeights _ _).trans
      (max_le ((weighted_add_le totalYRWeights _ _).trans (max_le h1 h2)) h3)) h4

lemma numerator_totalYR_wt_le (F : MvPolynomial (Fin 4) K) (L : ℕ)
    (hLpos : 2 ≤ L) (hF : WF F ≤ L) (r : ℕ) :
    WF (numerator K F r) ≤ 1 + 2 * r * (L - 1) := by
  induction r with
  | zero =>
      simp only [numerator_zero, Nat.mul_zero, Nat.zero_mul, Nat.add_zero]
      rw [wf_X]
      rfl
  | succ r ih =>
      rw [numerator_succ]
      have hh := numeratorStep_totalYR_wt_le F (numerator K F r) r
        (1 + 2 * r * (L - 1)) L (by omega) hLpos hF ih
      calc
        _ ≤ (1 + 2 * r * (L - 1)) + 2 * (L - 1) := hh
        _ = 1 + 2 * (r + 1) * (L - 1) := by ring

lemma shiftedX_totalYR_wt_zero (x : K) :
    WF (MvPolynomial.C x - MvPolynomial.X (0 : Fin 4) :
      MvPolynomial (Fin 4) K) = 0 := by
  apply Nat.eq_zero_of_le_zero
  apply (wf_sub_le _ _).trans
  rw [wf_C, wf_X]
  rfl

lemma commonNumeratorTerm_totalYR_wt_le
    (F : MvPolynomial (Fin 4) K) (L w j : ℕ) (hLpos : 2 ≤ L)
    (hj : j ≤ w) (hF : WF F ≤ L) (c : ℕ → K) (x : K) :
    WF (commonNumeratorTerm F w c x j) ≤ 1 + 2 * w * (L - 1) := by
  have hM := numerator_totalYR_wt_le F L hLpos hF j
  have hC : WF (MvPolynomial.C (c j) * numerator K F j) ≤
      1 + 2 * j * (L - 1) := by
    have hh := weighted_mul_le totalYRWeights (MvPolynomial.C (c j))
      (numerator K F j)
    rw [wf_C, zero_add] at hh
    exact hh.trans hM
  have hH := polyH_wf_le F L hF
  have hHP := (wf_pow_le (polyH K F) (2 * (w - j))).trans
    (Nat.mul_le_mul_left (2 * (w - j)) hH)
  have hX := wf_pow_le
    (MvPolynomial.C x - MvPolynomial.X (0 : Fin 4) : MvPolynomial (Fin 4) K) j
  rw [shiftedX_totalYR_wt_zero x, Nat.mul_zero] at hX
  have hh1 := weighted_mul_le totalYRWeights
    (MvPolynomial.C (c j) * numerator K F j) (polyH K F ^ (2 * (w - j)))
  have hh2 := weighted_mul_le totalYRWeights
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

lemma clearedTaylorNumerator_totalYR_wt_le
    (F : MvPolynomial (Fin 4) K) (L w : ℕ) (hLpos : 2 ≤ L)
    (hF : WF F ≤ L) (c : ℕ → K) (x : K) :
    WF (clearedTaylorNumerator F w c x) ≤ 1 + 2 * w * (L - 1) := by
  unfold clearedTaylorNumerator
  apply wf_sum_le
  intro j hj
  exact commonNumeratorTerm_totalYR_wt_le F L w j hLpos
    (by have hh := Finset.mem_range.mp hj; omega) hF c x

lemma affineSeedPolynomial_totalYR_wt_le (u₀ u₁ : K) :
    WF (affineSeedPolynomial u₀ u₁ : MvPolynomial (Fin 4) K) ≤ 1 := by
  unfold affineSeedPolynomial
  apply (weighted_add_le totalYRWeights _ _).trans
  apply max_le
  · rw [wf_C]; omega
  · have hh := weighted_mul_le totalYRWeights (MvPolynomial.X (3 : Fin 4))
      (MvPolynomial.C u₁)
    rw [wf_X, wf_C, Nat.add_zero] at hh
    simp [totalYRWeights] at hh
    have hh0 : WF (MvPolynomial.X (3 : Fin 4) * MvPolynomial.C u₁) = 0 := by
      simpa only [totalYRWeights] using hh
    exact hh0.le.trans (Nat.zero_le 1)

lemma agreementNumerator_totalYR_wt_le
    (F : MvPolynomial (Fin 4) K) (L w : ℕ) (hLpos : 2 ≤ L)
    (hF : WF F ≤ L) (c : ℕ → K) (x u₀ u₁ : K) :
    WF (agreementNumerator F w c x u₀ u₁) ≤ 1 + 2 * w * (L - 1) := by
  unfold agreementNumerator
  apply (wf_sub_le _ _).trans
  apply max_le (clearedTaylorNumerator_totalYR_wt_le F L w hLpos hF c x)
  have hH := polyH_wf_le F L hF
  have hHP := (wf_pow_le (polyH K F) (2 * w)).trans
    (Nat.mul_le_mul_left (2 * w) hH)
  have hh := weighted_mul_le totalYRWeights (affineSeedPolynomial u₀ u₁)
    (polyH K F ^ (2 * w))
  have ha := affineSeedPolynomial_totalYR_wt_le (K := K) u₀ u₁
  omega


lemma agreementNumerator_Y_degree_cap_totalYR
    (F : MvPolynomial (Fin 4) K) (c w : ℕ) (hcpos : 2 ≤ c)
    (hF : WF F ≤ c) (coeffs : ℕ → K) (x u₀ u₁ : K) :
    (agreementNumerator F w coeffs x u₀ u₁).degreeOf (1 : Fin 4) ≤
      1 + 2 * w * (c - 1) := by
  apply MvPolynomial.degreeOf_le_iff.mpr
  intro d hd
  have hdegree := (MvPolynomial.le_weightedTotalDegree totalYRWeights hd).trans
    (agreementNumerator_totalYR_wt_le F c w hcpos hF coeffs x u₀ u₁)
  rw [totalYR_weight] at hdegree
  omega

theorem surface_agreement_Y_degree_cap_totalYR
    (φ : Polynomial K →+* Ω) (F : MvPolynomial (Fin 4) K)
    (c w : ℕ) (hcpos : 2 ≤ c) (hF : WF F ≤ c)
    (coeffs : ℕ → K) (x u₀ u₁ : K) :
    (surfaceMap φ (agreementNumerator F w coeffs x u₀ u₁)).degreeOf 0 ≤
      1 + 2 * w * (c - 1) :=
  (surfaceMap_degreeOf_le φ _ 0).trans
    (agreementNumerator_Y_degree_cap_totalYR F c w hcpos hF coeffs x u₀ u₁)

end

end ProximityPrize.SubmissionLower.ContactSharpTotalAgreement

#print axioms ProximityPrize.SubmissionLower.ContactSharpTotalAgreement.totalYR_wt_le_of_mem_box
#print axioms ProximityPrize.SubmissionLower.ContactSharpTotalAgreement.agreementNumerator_totalYR_wt_le
#print axioms ProximityPrize.SubmissionLower.ContactSharpTotalAgreement.surface_agreement_Y_degree_cap_totalYR
