import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactFactorCaps
import ProximityPrize.SubmissionLower.ContactTaylorNumerators
import ProximityPrize.SubmissionLower.ContactGenericSurface

/-! .






 -/

namespace ProximityPrize.SubmissionLower.ContactJointSeedCaps

open scoped BigOperators
open ContactInterpolation ContactFactorCaps ContactTaylorNumerators
  ContactGenericSurface

noncomputable section

variable {K Ω : Type} [Field K] [Field Ω]

abbrev Poly4 (K : Type) [Field K] := MvPolynomial (Fin 4) K

def seedDegree (P : Poly4 K) : ℕ :=
  MvPolynomial.weightedTotalDegree seedWeights P

theorem seedDegree_mul_le (P Q : Poly4 K) :
    seedDegree (P * Q) ≤ seedDegree P + seedDegree Q := by
  unfold seedDegree
  rw [← degree_weightedLift, map_mul]
  simpa only [degree_weightedLift] using
    MvPolynomial.degreeOf_mul_le (4 : Fin 5)
      (weightedLift K seedWeights P) (weightedLift K seedWeights Q)

theorem seedDegree_add_le (P Q : Poly4 K) :
    seedDegree (P + Q) ≤ max (seedDegree P) (seedDegree Q) := by
  unfold seedDegree
  rw [← degree_weightedLift, map_add]
  simpa only [degree_weightedLift] using
    MvPolynomial.degreeOf_add_le (4 : Fin 5)
      (weightedLift K seedWeights P) (weightedLift K seedWeights Q)

theorem seedDegree_sub_le (P Q : Poly4 K) :
    seedDegree (P - Q) ≤ max (seedDegree P) (seedDegree Q) := by
  unfold seedDegree
  rw [← degree_weightedLift, map_sub]
  simpa only [degree_weightedLift] using
    MvPolynomial.degreeOf_sub_le (4 : Fin 5)
      (weightedLift K seedWeights P) (weightedLift K seedWeights Q)

@[simp] theorem seedDegree_neg (P : Poly4 K) :
    seedDegree (-P) = seedDegree P := by
  unfold seedDegree
  rw [← degree_weightedLift, map_neg, MvPolynomial.degreeOf_neg,
    degree_weightedLift]

theorem seedDegree_pow_le (P : Poly4 K) (n : ℕ) :
    seedDegree (P ^ n) ≤ n * seedDegree P := by
  unfold seedDegree
  rw [← degree_weightedLift, map_pow]
  simpa only [degree_weightedLift] using
    MvPolynomial.degreeOf_pow_le (4 : Fin 5) (weightedLift K seedWeights P) n

theorem seedDegree_C (c : K) : seedDegree (MvPolynomial.C c : Poly4 K) = 0 := by
  unfold seedDegree MvPolynomial.weightedTotalDegree
  simp

theorem seedDegree_X (i : Fin 4) :
    seedDegree (MvPolynomial.X i : Poly4 K) = seedWeights i := by
  unfold seedDegree MvPolynomial.weightedTotalDegree
  simp [MvPolynomial.support_X, Finsupp.weight_single]

theorem seedDegree_natCast (n : ℕ) : seedDegree (n : Poly4 K) = 0 := by
  rw [← map_natCast (MvPolynomial.C : K →+* Poly4 K), seedDegree_C]

theorem seedDegree_pderiv_le (P : Poly4 K) (i : Fin 4) :
    seedDegree (MvPolynomial.pderiv i P) ≤ seedDegree P := by
  apply (weightedTotalDegree_le_iff seedWeights _ _).mpr
  intro e he
  have hd := support_before_pderiv i P e he
  have hmono : Finsupp.weight seedWeights e ≤
      Finsupp.weight seedWeights (e + Finsupp.single i 1) := by
    rw [map_add]
    exact Nat.le_add_right _ _
  exact hmono.trans (MvPolynomial.le_weightedTotalDegree seedWeights hd)

theorem seedDegree_sum_le (I : Finset ℕ) (f : ℕ → Poly4 K) (a : ℕ)
    (hf : ∀ i ∈ I, seedDegree (f i) ≤ a) :
    seedDegree (∑ i ∈ I, f i) ≤ a := by
  unfold seedDegree
  rw [← degree_weightedLift, map_sum]
  apply (MvPolynomial.degreeOf_sum_le (4 : Fin 5) I
    (fun i => weightedLift K seedWeights (f i))).trans
  apply Finset.sup_le
  intro i hi
  rw [degree_weightedLift]
  exact hf i hi

theorem seedDegree_polyH_le (F : Poly4 K) :
    seedDegree (polyH K F) ≤ seedDegree F :=
  seedDegree_pderiv_le F 2

theorem seedDegree_polyG_le (F : Poly4 K) :
    seedDegree (polyG K F) ≤ seedDegree F := by
  unfold polyG
  have hX := seedDegree_pderiv_le F 0
  have hY := seedDegree_pderiv_le F 1
  have hR : seedDegree (MvPolynomial.X (2 : Fin 4) : Poly4 K) = 0 := by
    simp [seedDegree_X, seedWeights]
  have hm := seedDegree_mul_le
    (MvPolynomial.X (2 : Fin 4) : Poly4 K) (MvPolynomial.pderiv 1 F)
  rw [hR, zero_add] at hm
  have hadd := (seedDegree_add_le (MvPolynomial.pderiv 0 F)
    (MvPolynomial.X (2 : Fin 4) * MvPolynomial.pderiv 1 F)).trans
      (max_le hX (hm.trans hY))
  rw [seedDegree_neg]
  exact hadd

/-- .
 -/
theorem numeratorStep_seedDegree_le
    (F M : Poly4 K) (b a L : ℕ)
    (hF : seedDegree F ≤ L) (hM : seedDegree M ≤ a) :
    seedDegree (numeratorStep K F b M) ≤ a + 2 * L := by
  let H := polyH K F
  let G := polyG K F
  let R : Poly4 K := MvPolynomial.X (2 : Fin 4)
  have hR : seedDegree R ≤ 0 := by simp [R, seedDegree_X, seedWeights]
  have hH : seedDegree H ≤ L := (seedDegree_polyH_le F).trans hF
  have hG : seedDegree G ≤ L := (seedDegree_polyG_le F).trans hF
  have hH2 := (seedDegree_pow_le H 2).trans (Nat.mul_le_mul_left 2 hH)
  have hMX : seedDegree (MvPolynomial.pderiv 0 M) ≤ a :=
    (seedDegree_pderiv_le M 0).trans hM
  have hMY : seedDegree (MvPolynomial.pderiv 1 M) ≤ a :=
    (seedDegree_pderiv_le M 1).trans hM
  have hMR : seedDegree (MvPolynomial.pderiv 2 M) ≤ a :=
    (seedDegree_pderiv_le M 2).trans hM
  have hHX : seedDegree (MvPolynomial.pderiv 0 H) ≤ L :=
    (seedDegree_pderiv_le H 0).trans hH
  have hHY : seedDegree (MvPolynomial.pderiv 1 H) ≤ L :=
    (seedDegree_pderiv_le H 1).trans hH
  have hHR : seedDegree (MvPolynomial.pderiv 2 H) ≤ L :=
    (seedDegree_pderiv_le H 2).trans hH
  have h1 : seedDegree (H ^ 2 * MvPolynomial.pderiv 0 M) ≤ a + 2 * L := by
    have hh := seedDegree_mul_le (H ^ 2) (MvPolynomial.pderiv 0 M)
    omega
  have h2 : seedDegree (R * H ^ 2 * MvPolynomial.pderiv 1 M) ≤ a + 2 * L := by
    have hh1 := seedDegree_mul_le R (H ^ 2)
    have hh2 := seedDegree_mul_le (R * H ^ 2) (MvPolynomial.pderiv 1 M)
    omega
  have h3 : seedDegree (G * H * MvPolynomial.pderiv 2 M) ≤ a + 2 * L := by
    have hh1 := seedDegree_mul_le G H
    have hh2 := seedDegree_mul_le (G * H) (MvPolynomial.pderiv 2 M)
    omega
  have hbx : seedDegree (H * MvPolynomial.pderiv 0 H) ≤ 2 * L := by
    have hh := seedDegree_mul_le H (MvPolynomial.pderiv 0 H)
    omega
  have hby : seedDegree (R * H * MvPolynomial.pderiv 1 H) ≤ 2 * L := by
    have hh1 := seedDegree_mul_le R H
    have hh2 := seedDegree_mul_le (R * H) (MvPolynomial.pderiv 1 H)
    omega
  have hbr : seedDegree (G * MvPolynomial.pderiv 2 H) ≤ 2 * L := by
    have hh := seedDegree_mul_le G (MvPolynomial.pderiv 2 H)
    omega
  have hbrace : seedDegree
      (H * MvPolynomial.pderiv 0 H + R * H * MvPolynomial.pderiv 1 H +
        G * MvPolynomial.pderiv 2 H) ≤ 2 * L := by
    exact (seedDegree_add_le _ _).trans
      (max_le ((seedDegree_add_le _ _).trans (max_le hbx hby)) hbr)
  have hn : seedDegree (((2 * b : ℕ) : Poly4 K)) ≤ 0 := by
    rw [seedDegree_natCast]
  have hnM : seedDegree (((2 * b : ℕ) : Poly4 K) * M) ≤ a := by
    have hh := seedDegree_mul_le (((2 * b : ℕ) : Poly4 K)) M
    omega
  have h4 : seedDegree (((2 * b : ℕ) : Poly4 K) * M *
      (H * MvPolynomial.pderiv 0 H + R * H * MvPolynomial.pderiv 1 H +
        G * MvPolynomial.pderiv 2 H)) ≤ a + 2 * L := by
    have hh := seedDegree_mul_le (((2 * b : ℕ) : Poly4 K) * M)
      (H * MvPolynomial.pderiv 0 H + R * H * MvPolynomial.pderiv 1 H +
        G * MvPolynomial.pderiv 2 H)
    omega
  change seedDegree
      (H ^ 2 * MvPolynomial.pderiv 0 M +
        R * H ^ 2 * MvPolynomial.pderiv 1 M +
        G * H * MvPolynomial.pderiv 2 M -
        ((2 * b : ℕ) : Poly4 K) * M *
          (H * MvPolynomial.pderiv 0 H + R * H * MvPolynomial.pderiv 1 H +
            G * MvPolynomial.pderiv 2 H)) ≤ a + 2 * L
  exact (seedDegree_sub_le _ _).trans
    (max_le ((seedDegree_add_le _ _).trans
      (max_le ((seedDegree_add_le _ _).trans (max_le h1 h2)) h3)) h4)

theorem numerator_seedDegree_le
    (F : Poly4 K) (L : ℕ) (hF : seedDegree F ≤ L) (b : ℕ) :
    seedDegree (numerator K F b) ≤ 1 + 2 * b * L := by
  induction b with
  | zero =>
      simp [numerator_zero, seedDegree_X, seedWeights]
  | succ b ih =>
      rw [numerator_succ]
      have hh := numeratorStep_seedDegree_le F (numerator K F b) b
        (1 + 2 * b * L) L hF ih
      convert hh using 1 <;> ring

theorem numerator_joint_seed_cap
    (F : Poly4 K) (L b : ℕ) (hF : seedDegree F ≤ L) :
    ∀ d ∈ (numerator K F b).support,
      d 1 + d 3 ≤ 1 + 2 * b * L := by
  intro d hd
  rw [← seed_weight]
  exact (MvPolynomial.le_weightedTotalDegree seedWeights hd).trans
    (numerator_seedDegree_le F L hF b)

/-- .
 -/
theorem surfaceMap_numerator_joint_seed_cap
    (φ : Polynomial K →+* Ω) (F : Poly4 K) (L b : ℕ)
    (hF : seedDegree F ≤ L) :
    ∀ d ∈ (surfaceMap φ (numerator K F b)).support,
      d 0 + d 2 ≤ 1 + 2 * b * L :=
  surfaceMap_joint_seed_cap φ _ _ (numerator_joint_seed_cap F L b hF)

theorem shiftedX_seedDegree_le (x : K) :
    seedDegree (MvPolynomial.C x - MvPolynomial.X (0 : Fin 4) : Poly4 K) ≤ 0 := by
  exact (seedDegree_sub_le _ _).trans (max_le (by simp [seedDegree_C])
    (by simp [seedDegree_X, seedWeights]))

theorem commonNumeratorTerm_seedDegree_le
    (F : Poly4 K) (L w j : ℕ) (hj : j ≤ w)
    (hF : seedDegree F ≤ L) (c : ℕ → K) (x : K) :
    seedDegree (commonNumeratorTerm F w c x j) ≤ 1 + 2 * w * L := by
  have hM := numerator_seedDegree_le F L hF j
  have hC : seedDegree (MvPolynomial.C (c j) : Poly4 K) ≤ 0 := by
    simp [seedDegree_C]
  have hCM := seedDegree_mul_le (MvPolynomial.C (c j) : Poly4 K) (numerator K F j)
  have hH := (seedDegree_polyH_le F).trans hF
  have hHP := (seedDegree_pow_le (polyH K F) (2 * (w - j))).trans
    (Nat.mul_le_mul_left (2 * (w - j)) hH)
  have hXP := (seedDegree_pow_le
    (MvPolynomial.C x - MvPolynomial.X (0 : Fin 4) : Poly4 K) j).trans
      (Nat.mul_le_mul_left j (shiftedX_seedDegree_le x))
  have h1 := seedDegree_mul_le
    (MvPolynomial.C (c j) * numerator K F j)
    (polyH K F ^ (2 * (w - j)))
  have h2 := seedDegree_mul_le
    (MvPolynomial.C (c j) * numerator K F j * polyH K F ^ (2 * (w - j)))
    ((MvPolynomial.C x - MvPolynomial.X (0 : Fin 4)) ^ j)
  have hw : j + (w - j) = w := by omega
  dsimp [commonNumeratorTerm]
  have hCMcap : seedDegree
      (MvPolynomial.C (c j) * numerator K F j) ≤ 1 + 2 * j * L := by
    exact hCM.trans (Nat.add_le_add hC hM) |>.trans (by omega)
  have h1cap : seedDegree
      (MvPolynomial.C (c j) * numerator K F j * polyH K F ^ (2 * (w - j))) ≤
      (1 + 2 * j * L) + 2 * (w - j) * L :=
    h1.trans (Nat.add_le_add hCMcap hHP)
  have hterm := h2.trans (Nat.add_le_add h1cap hXP)
  calc
    seedDegree
        (MvPolynomial.C (c j) * numerator K F j * polyH K F ^ (2 * (w - j)) *
          (MvPolynomial.C x - MvPolynomial.X 0) ^ j) ≤
        ((1 + 2 * j * L) + 2 * (w - j) * L) + j * 0 := hterm
    _ = 1 + 2 * (j + (w - j)) * L := by ring
    _ = 1 + 2 * w * L := by rw [hw]

theorem clearedTaylorNumerator_seedDegree_le
    (F : Poly4 K) (L w : ℕ) (hF : seedDegree F ≤ L)
    (c : ℕ → K) (x : K) :
    seedDegree (clearedTaylorNumerator F w c x) ≤ 1 + 2 * w * L := by
  unfold clearedTaylorNumerator
  apply seedDegree_sum_le
  intro j hj
  exact commonNumeratorTerm_seedDegree_le F L w j
    (by have hh := Finset.mem_range.mp hj; omega) hF c x

theorem affineSeedPolynomial_seedDegree_le (u₀ u₁ : K) :
    seedDegree (affineSeedPolynomial u₀ u₁) ≤ 1 := by
  unfold affineSeedPolynomial
  have hC0 : seedDegree (MvPolynomial.C u₀ : Poly4 K) ≤ 0 := by simp [seedDegree_C]
  have hZ : seedDegree (MvPolynomial.X (3 : Fin 4) : Poly4 K) ≤ 1 := by
    simp [seedDegree_X, seedWeights]
  have hC1 : seedDegree (MvPolynomial.C u₁ : Poly4 K) ≤ 0 := by simp [seedDegree_C]
  have hm := seedDegree_mul_le (MvPolynomial.X (3 : Fin 4) : Poly4 K)
    (MvPolynomial.C u₁)
  exact (seedDegree_add_le _ _).trans (max_le (hC0.trans (by omega)) (by omega))

/-- .
 -/
theorem agreementNumerator_seedDegree_le
    (F : Poly4 K) (L w : ℕ) (hF : seedDegree F ≤ L)
    (c : ℕ → K) (x u₀ u₁ : K) :
    seedDegree (agreementNumerator F w c x u₀ u₁) ≤ 1 + 2 * w * L := by
  unfold agreementNumerator
  have ht := clearedTaylorNumerator_seedDegree_le F L w hF c x
  have ha := affineSeedPolynomial_seedDegree_le u₀ u₁
  have hH := (seedDegree_polyH_le F).trans hF
  have hp := (seedDegree_pow_le (polyH K F) (2 * w)).trans
    (Nat.mul_le_mul_left (2 * w) hH)
  have hm := seedDegree_mul_le (affineSeedPolynomial u₀ u₁) (polyH K F ^ (2 * w))
  exact (seedDegree_sub_le _ _).trans (max_le ht (by omega))

theorem agreementNumerator_joint_seed_cap
    (F : Poly4 K) (L w : ℕ) (hF : seedDegree F ≤ L)
    (c : ℕ → K) (x u₀ u₁ : K) :
    ∀ d ∈ (agreementNumerator F w c x u₀ u₁).support,
      d 1 + d 3 ≤ 1 + 2 * w * L := by
  intro d hd
  rw [← seed_weight]
  exact (MvPolynomial.le_weightedTotalDegree seedWeights hd).trans
    (agreementNumerator_seedDegree_le F L w hF c x u₀ u₁)

/-- .
 -/
theorem surfaceMap_agreement_joint_seed_cap
    (φ : Polynomial K →+* Ω) (F : Poly4 K) (L w : ℕ)
    (hF : seedDegree F ≤ L) (c : ℕ → K) (x u₀ u₁ : K) :
    ∀ d ∈ (surfaceMap φ (agreementNumerator F w c x u₀ u₁)).support,
      d 0 + d 2 ≤ 1 + 2 * w * L :=
  surfaceMap_joint_seed_cap φ _ _
    (agreementNumerator_joint_seed_cap F L w hF c x u₀ u₁)

end


end ProximityPrize.SubmissionLower.ContactJointSeedCaps
