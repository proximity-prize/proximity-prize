import ProximityPrize.SubmissionBinaryLower.Binary6402Table4KPart2
import ProximityPrize.SubmissionBinaryLower.Binary6402Table4Common
import ProximityPrize.SubmissionBinaryLower.Binary6402Table4NonK

set_option Elab.async false
set_option maxHeartbeats 2400000
set_option maxRecDepth 1024

/-!
# Table 4B (`K ≠ 0`, 84 branches) and Top-Level Table 4 Exhaustive Algebra Dichotomy

Proves:
1. `table4_K_sat`: for any `S : KerD45Syzygy D` with `S.P0 = 0` and `S.M21 ≠ 0`, `D` produces an
   exact `T4BBranch` (`rGt ∈ Bool`, `vCancel ∈ Bool`, `q1Case < 3`, `odeCase < 7`) and an explicit
   nonnegative `x : Fin 49 → ℚ` satisfying ALL rows of `B6402T4Rows.buildT4BRows br`!
2. `table4_algebra_dichotomy`: for ANY `D : KerD45Data`, EITHER `EscapeUZero D`, OR `D` satisfies
   one of the 36 Table 4A branches (`T4ABranch`) OR one of the 84 Table 4B branches (`T4BBranch`)!
-/

namespace ProximityPrize.SubmissionBinaryLower
namespace B6402Table4K

open B6401Params hiding A
open B6402HybridP64 (A)
open Polynomial B6401ContactKerD B6401QuotInterp B6401ResultantOrd
open B6401KerDOrders B6402IntFarkas B6402T4Rows B6401Char2ODE B6402Table4Common B6402Table4NonK
open ProximityPrize.Benchmark ProximityPrize.Benchmark.Binary
open scoped BigOperators

local notation (priority := high) "X" => Polynomial.X
local notation "Fld" => BinaryIRSProfile.Field
local notation "Idx" => BinaryIRSProfile.Index
namespace KerD45KData
variable {D : KerD45Data} {S : KerD45Syzygy D} (K : KerD45KData S)

lemma H1_d2_bound :
    4 * K.d2k0Cnt + 3 * K.d2k1UCnt + S.n1U + 3 * S.n2U + 3 * S.n3U + 2 * D.n3 + 2 * D.nt ≤ S.H1.natDegree := by
  classical
  let f : Idx → ℕ := fun i =>
    if D.k i = 0 ∧ K.isD1 i then 4
    else if D.k i = 1 ∧ S.isU0 i ∧ K.isD1 i then 4
    else if S.isU0 i then 2 * D.k i - 1
    else 2 * (D.k i - 2)
  have hdvd : ∀ i ∈ (Finset.univ : Finset Idx), (X - C (BinaryIRSProfile.domain i)) ^ f i ∣ S.H1 := fun i _ => by
    dsimp [f]; split_ifs with h0 h1 hU
    · exact ((pow_dvd_pow _ (by omega : 4 ≤ 5)).trans (pow_dvd_pow_of_dvd (dvd_iff_isRoot.mpr h0.2) 5)).trans S.D1_pow5_dvd_H1
    · exact ((pow_dvd_pow _ (by omega : 4 ≤ 5)).trans (pow_dvd_pow_of_dvd (dvd_iff_isRoot.mpr h1.2.2) 5)).trans S.D1_pow5_dvd_H1
    · exact S.pow_dvd_H1_of_isU0 i hU
    · exact K.pow_dvd_H1_U1 i hU
  have hle := sum_ord_le_natDegree_of_dvd Finset.univ BinaryIRSProfile.domain BinaryIRSProfile.domain.injective
    S.H1 S.H1_ne_zero f hdvd
  have hZ : (4 * (K.d2k0Cnt : ℤ) + 3 * (K.d2k1UCnt : ℤ) + (S.n1U : ℤ) + 3 * (S.n2U : ℤ) +
      3 * (S.n3U : ℤ) + 2 * (D.n3 : ℤ) + 2 * (D.nt : ℤ)) = ∑ i : Idx, (f i : ℤ) := by
    have hrew : 4 * (K.d2k0Cnt : ℤ) + 3 * (K.d2k1UCnt : ℤ) + (S.n1U : ℤ) + 3 * (S.n2U : ℤ) +
        3 * (S.n3U : ℤ) + 2 * (D.n3 : ℤ) + 2 * (D.nt : ℤ) =
        ∑ i : Idx, (4 * (if D.k i = 0 ∧ K.isD1 i then (1 : ℤ) else 0) +
          3 * (if D.k i = 1 ∧ S.isU0 i ∧ K.isD1 i then 1 else 0) +
          (if D.k i = 1 ∧ S.isU0 i then 1 else 0) +
          3 * (if D.k i = 2 ∧ S.isU0 i then 1 else 0) +
          3 * (if 3 ≤ D.k i ∧ S.isU0 i then 1 else 0) +
          2 * (if 3 ≤ D.k i then 1 else 0) + 2 * ((D.k i - 3 : ℕ) : ℤ)) := by
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
        ← n0_Z, ← n1_Z, ← n2_Z, ← n3_Z, ← nt_Z, ← n1U_Z, ← n2U_Z, ← n3U_Z,
        ← K.mbadCnt_Z, ← K.mLCnt_Z, ← K.din2Cnt_Z, ← K.din3Cnt_Z, ← K.dmL2Cnt_Z, ← K.dmL3Cnt_Z,
        ← K.d2k1UCnt_Z, ← K.d2k0Cnt_Z, ← K.mu1Cnt_Z, ← K.ntUNorm_Z, ← K.ntUMbad_Z, ← K.ntUML_Z, ← K.muExK3_Z] <;> ring
    rw [hrew]; apply Finset.sum_congr rfl; intro i _; dsimp [f]
    by_cases hU : S.isU0 i <;> by_cases hD1 : K.isD1 i <;>
      simp only [hU, hD1, and_true, and_false, true_and, false_and, ↓reduceIte] <;>
      (try split_ifs) <;> omega
  rw [← Nat.cast_sum] at hZ; omega

lemma Lam1_M0s_U_bound :
    (D.n1 - S.n1U) + (2 * D.n2 - S.n2U) + (4 * D.n3 - S.n3U) + 2 * D.nt ≤ K.Lam1.natDegree + K.M0s.natDegree := by
  classical
  let f : Idx → ℕ := fun i =>
    if S.isU0 i then (if D.k i ≤ 1 then 0 else 2 * D.k i - 3)
    else (if D.k i = 0 then 0 else if D.k i = 1 then 1 else 2 * D.k i - 2)
  have hle := sum_ord_le_natDegree_of_dvd Finset.univ (fun i => BinaryIRSProfile.domain i ^ 2)
    domain_sq_injective (K.Lam1 * K.M0s) (mul_ne_zero K.hLam1_ne K.hM0s_ne) f (fun i _ => K.pow_dvd_Lam1_mul_M0s i)
  rw [natDegree_mul K.hLam1_ne K.hM0s_ne] at hle
  have hU := S.U_counts_ineqs
  have hZ : (((D.n1 : ℤ) - (S.n1U : ℤ)) + (2 * (D.n2 : ℤ) - (S.n2U : ℤ)) +
      (4 * (D.n3 : ℤ) - (S.n3U : ℤ)) + 2 * (D.nt : ℤ)) = ∑ i : Idx, (f i : ℤ) := by
    have hrew : ((D.n1 : ℤ) - (S.n1U : ℤ)) + (2 * (D.n2 : ℤ) - (S.n2U : ℤ)) +
        (4 * (D.n3 : ℤ) - (S.n3U : ℤ)) + 2 * (D.nt : ℤ) =
        ∑ i : Idx, ((if D.k i = 1 then (1 : ℤ) else 0) - (if D.k i = 1 ∧ S.isU0 i then 1 else 0) +
          2 * (if D.k i = 2 then 1 else 0) - (if D.k i = 2 ∧ S.isU0 i then 1 else 0) +
          4 * (if 3 ≤ D.k i then 1 else 0) - (if 3 ≤ D.k i ∧ S.isU0 i then 1 else 0) +
          2 * ((D.k i - 3 : ℕ) : ℤ)) := by
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
        ← n0_Z, ← n1_Z, ← n2_Z, ← n3_Z, ← nt_Z, ← n1U_Z, ← n2U_Z, ← n3U_Z,
        ← K.mbadCnt_Z, ← K.mLCnt_Z, ← K.din2Cnt_Z, ← K.din3Cnt_Z, ← K.dmL2Cnt_Z, ← K.dmL3Cnt_Z,
        ← K.d2k1UCnt_Z, ← K.d2k0Cnt_Z, ← K.mu1Cnt_Z, ← K.ntUNorm_Z, ← K.ntUMbad_Z, ← K.ntUML_Z, ← K.muExK3_Z] <;> ring
    rw [hrew]; apply Finset.sum_congr rfl; intro i _; dsimp [f]
    by_cases hU : S.isU0 i <;>
      simp only [hU, and_true, and_false, true_and, false_and, ↓reduceIte] <;>
      (try split_ifs) <;> omega
  rw [← Nat.cast_sum] at hZ; omega

lemma K_tot_bound :
    2 * K.dinCnt + K.dmLCnt + K.mLCnt + (D.n2 - S.n2U) + (3 * D.n3 - S.n3U) + 2 * D.nt ≤
      K.K1.natDegree + K.Lam1.natDegree := by
  classical
  let f : Idx → ℕ := fun i =>
    if D.k i ≤ 1 then 0
    else if ¬ S.isU0 i then (if D.k i = 2 then 1 else 3 + 2 * (D.k i - 3))
    else if K.isD1 i then (if K.isNorm i ∨ K.isML i then 2 * D.k i - 2 else 0)
    else if K.isML i then (if D.k i = 2 then 1 else 3 + 2 * (D.k i - 3))
    else 2 * D.k i - 4
  have hdvd : ∀ i ∈ (Finset.univ : Finset Idx), (X - C (BinaryIRSProfile.domain i ^ 2)) ^ f i ∣ K.K1 * K.Lam1 := fun i _ => by
    dsimp only [f]
    by_cases hk1 : D.k i ≤ 1
    · simp [hk1]
    · simp only [hk1, ↓reduceIte]
      by_cases hU : S.isU0 i
      · simp only [hU, not_true_eq_false, ↓reduceIte]
        by_cases hD1 : K.isD1 i
        · simp only [hD1, ↓reduceIte]
          by_cases hNM : K.isNorm i ∨ K.isML i
          · simp only [hNM, ↓reduceIte]
            have h := K.pow_dvd_K_M10sh_d2 i hD1; simp only [hk1, ↓reduceIte] at h; exact h
          · simp [hNM]
        · simp only [hD1, ↓reduceIte]
          by_cases hmL : K.isML i
          · simp only [hmL, ↓reduceIte]
            have hK1d := K.pow_dvd_K1_all i
            have hL1d : (X - C (BinaryIRSProfile.domain i ^ 2)) ^ (2 * D.k i - 3) ∣ K.Lam1 := by
              have hprod := K.pow_dvd_Lam1_mul_M0s i
              simp only [hU, hk1, ↓reduceIte] at hprod
              have hcop := ((Polynomial.irreducible_X_sub_C (BinaryIRSProfile.domain i ^ 2)).coprime_iff_not_dvd.mpr
                (mt dvd_iff_isRoot.mp hmL.2.2.2)).pow_left (m := 2 * D.k i - 3)
              exact hcop.dvd_of_dvd_mul_right hprod
            exact (pow_dvd_pow _ (by split_ifs <;> omega : (if D.k i = 2 then 1 else 3 + 2 * (D.k i - 3)) ≤ (D.k i - 2) + (2 * D.k i - 3))).trans
              (by rw [pow_add]; exact mul_dvd_mul hK1d hL1d)
          · simp only [hmL, ↓reduceIte]
            exact K.pow_dvd_K_U0_D1_ne i hU hD1
      · simp only [hU, not_false_eq_true, ↓reduceIte]
        have h := K.pow_dvd_K_U1 i hU; simp only [show D.k i ≠ 0 by omega, ↓reduceIte] at h
        exact (pow_dvd_pow _ (by split_ifs <;> omega : (if D.k i = 2 then 1 else 3 + 2 * (D.k i - 3)) ≤ 2 * D.k i - 1)).trans h
  have hle := sum_ord_le_natDegree_of_dvd Finset.univ (fun i => BinaryIRSProfile.domain i ^ 2)
    domain_sq_injective (K.K1 * K.Lam1) (mul_ne_zero K.hK1_ne K.hLam1_ne) f hdvd
  rw [natDegree_mul K.hK1_ne K.hLam1_ne] at hle
  have hU := S.U_counts_ineqs
  have hZ : (2 * (K.dinCnt : ℤ) + (K.dmLCnt : ℤ) + (K.mLCnt : ℤ) + ((D.n2 : ℤ) - (S.n2U : ℤ)) +
      (3 * (D.n3 : ℤ) - (S.n3U : ℤ)) + 2 * (D.nt : ℤ)) = ∑ i : Idx, (f i : ℤ) := by
    have hrew : 2 * (K.dinCnt : ℤ) + (K.dmLCnt : ℤ) + (K.mLCnt : ℤ) + ((D.n2 : ℤ) - (S.n2U : ℤ)) +
        (3 * (D.n3 : ℤ) - (S.n3U : ℤ)) + 2 * (D.nt : ℤ) =
        ∑ i : Idx, (2 * (if D.k i = 2 ∧ K.isNorm i ∧ K.isD1 i then (1 : ℤ) else 0) +
          2 * (if 3 ≤ D.k i ∧ K.isNorm i ∧ K.isD1 i then 1 else 0) +
          (if D.k i = 2 ∧ K.isML i ∧ K.isD1 i then 1 else 0) +
          (if 3 ≤ D.k i ∧ K.isML i ∧ K.isD1 i then 1 else 0) +
          (if K.isML i then 1 else 0) +
          (if D.k i = 2 then 1 else 0) - (if D.k i = 2 ∧ S.isU0 i then 1 else 0) +
          3 * (if 3 ≤ D.k i then 1 else 0) - (if 3 ≤ D.k i ∧ S.isU0 i then 1 else 0) +
          2 * ((D.k i - 3 : ℕ) : ℤ)) := by
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
        ← n0_Z, ← n1_Z, ← n2_Z, ← n3_Z, ← nt_Z, ← n1U_Z, ← n2U_Z, ← n3U_Z,
        ← K.mbadCnt_Z, ← K.mLCnt_Z, ← K.din2Cnt_Z, ← K.din3Cnt_Z, ← K.dmL2Cnt_Z, ← K.dmL3Cnt_Z,
        ← K.d2k1UCnt_Z, ← K.d2k0Cnt_Z, ← K.mu1Cnt_Z, ← K.ntUNorm_Z, ← K.ntUMbad_Z, ← K.ntUML_Z, ← K.muExK3_Z]
      simp only [dinCnt, dmLCnt, Nat.cast_add]; ring
    rw [hrew]; apply Finset.sum_congr rfl; intro i _
    dsimp [f]
    by_cases hD1 : K.isD1 i
    · have hU' : S.isU0 i := K.isU0_of_D1_zero hD1
      have hg0 : K.g2t.eval (BinaryIRSProfile.domain i) = 0 := K.g2t_zero_of_D1_zero hD1
      by_cases hm : K.M0s.eval (BinaryIRSProfile.domain i ^ 2) = 0 <;>
        simp only [isNorm, isML, hD1, hU', hg0, hm, ne_eq, not_true_eq_false, not_false_eq_true,
          and_true, and_false, true_and, false_and, or_true, or_false, true_or, false_or, ↓reduceIte] <;>
        (try split_ifs) <;> omega
    · by_cases hU' : S.isU0 i <;> by_cases hg0 : K.g2t.eval (BinaryIRSProfile.domain i) = 0 <;>
        by_cases hm : K.M0s.eval (BinaryIRSProfile.domain i ^ 2) = 0 <;>
        simp only [isNorm, isML, hD1, hU', hg0, hm, ne_eq, not_true_eq_false, not_false_eq_true,
          and_true, and_false, true_and, false_and, or_true, or_false, true_or, false_or, ↓reduceIte] <;>
        (try split_ifs) <;> omega
  rw [← Nat.cast_sum] at hZ; omega

/-! #### Degree identities and Sylvester / minor degree bounds -/

lemma natDegree_p_eq : S.p.natDegree = S.D1.natDegree + K.p1.natDegree := by
  rw [K.hp_fac, natDegree_mul S.D2_ne_zero K.hp1_ne, ← S.D1_natDegree]

lemma natDegree_g1_eq : (D.gj 1).natDegree = 2 * K.K1.natDegree + K.g2t.natDegree := by
  rw [K.hg1_fac, natDegree_mul (mt (comp_X_sq_eq_zero_iff K.K1).mp K.hK1_ne) K.hg2t_ne, natDegree_comp_X_sq]

lemma natDegree_H1_eq : S.H1.natDegree = 4 * S.D1.natDegree + 2 * K.M0s.natDegree + K.g2t.natDegree := by
  have hM_ne := mt (comp_X_sq_eq_zero_iff K.M0s).mp K.hM0s_ne
  rw [K.hH1_fac, natDegree_mul (mul_ne_zero (pow_ne_zero 4 S.D1_ne_zero) hM_ne) K.hg2t_ne,
    natDegree_mul (pow_ne_zero 4 S.D1_ne_zero) hM_ne, natDegree_pow, natDegree_comp_X_sq]

lemma natDegree_ResY_eq :
    D.ResY.natDegree = 4 * S.D1.natDegree + 8 * K.Lam1.natDegree + 10 * K.M0s.natDegree + K.g2t.natDegree := by
  have hL_ne := mt (comp_X_sq_eq_zero_iff K.Lam1).mp K.hLam1_ne
  have hM_ne := mt (comp_X_sq_eq_zero_iff K.M0s).mp K.hM0s_ne
  rw [K.hResY_fac,
    natDegree_mul (mul_ne_zero (mul_ne_zero (pow_ne_zero 4 S.D1_ne_zero) (pow_ne_zero 4 hL_ne)) (pow_ne_zero 5 hM_ne)) K.hg2t_ne,
    natDegree_mul (mul_ne_zero (pow_ne_zero 4 S.D1_ne_zero) (pow_ne_zero 4 hL_ne)) (pow_ne_zero 5 hM_ne),
    natDegree_mul (pow_ne_zero 4 S.D1_ne_zero) (pow_ne_zero 4 hL_ne),
    natDegree_pow, natDegree_pow, natDegree_pow, natDegree_comp_X_sq, natDegree_comp_X_sq]
  ring

lemma row338_bound :
    2 * (5 * S.p.natDegree - 2 * S.D1.natDegree + K.K1.natDegree + K.Lam1.natDegree) ≤
      (D.gj 2).natDegree + (D.gj 1).natDegree := by
  have hM21_ne : S.M21 ≠ 0 := by
    rw [K.hM21_fac]; exact mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero 2 S.D2_ne_zero) (pow_ne_zero 4 K.hp1_ne)) K.hK1_ne) K.hLam1_ne
  have hdeg_pM21 : (S.p * S.M21).natDegree = 5 * S.p.natDegree - 2 * S.D1.natDegree + K.K1.natDegree + K.Lam1.natDegree := by
    rw [natDegree_mul S.hp hM21_ne, K.hM21_fac,
      natDegree_mul (mul_ne_zero (mul_ne_zero (pow_ne_zero 2 S.D2_ne_zero) (pow_ne_zero 4 K.hp1_ne)) K.hK1_ne) K.hLam1_ne,
      natDegree_mul (mul_ne_zero (pow_ne_zero 2 S.D2_ne_zero) (pow_ne_zero 4 K.hp1_ne)) K.hK1_ne,
      natDegree_mul (pow_ne_zero 2 S.D2_ne_zero) (pow_ne_zero 4 K.hp1_ne),
      natDegree_pow, natDegree_pow, ← S.D1_natDegree]
    have hp := K.natDegree_p_eq; omega
  rw [← hdeg_pM21, S.p_mul_M21]
  have ht1 : 2 * (D.Cj 2 * D.Bj 1).natDegree ≤ (D.gj 2).natDegree + (D.gj 1).natDegree := by
    by_cases h0 : D.Cj 2 = 0 ∨ D.Bj 1 = 0
    · rcases h0 with h | h <;> simp [h]
    · push Not at h0
      have h1 := two_mul_natDegree_le_even_odd (D.Cj 2) (D.Bj 2) h0.1
      have h2 := two_mul_natDegree_add_one_le_even_odd (D.Cj 1) (D.Bj 1) h0.2
      have h3 := natDegree_mul_le (p := D.Cj 2) (q := D.Bj 1)
      unfold KerD45Data.gj at *; omega
  have ht2 : 2 * (D.Cj 1 * D.Bj 2).natDegree ≤ (D.gj 2).natDegree + (D.gj 1).natDegree := by
    by_cases h0 : D.Cj 1 = 0 ∨ D.Bj 2 = 0
    · rcases h0 with h | h <;> simp [h]
    · push Not at h0
      have h1 := two_mul_natDegree_le_even_odd (D.Cj 1) (D.Bj 1) h0.1
      have h2 := two_mul_natDegree_add_one_le_even_odd (D.Cj 2) (D.Bj 2) h0.2
      have h3 := natDegree_mul_le (p := D.Cj 1) (q := D.Bj 2)
      unfold KerD45Data.gj at *; omega
  have hadd := natDegree_add_le (D.Cj 2 * D.Bj 1) (D.Cj 1 * D.Bj 2)
  omega

lemma row339_bound :
    4 * (S.p.natDegree : ℤ) + 4 * (K.K1.natDegree : ℤ) + 4 * (K.Lam1.natDegree : ℤ) +
      8 * (S.R.natDegree : ℤ) - 8 * (S.D1.natDegree : ℤ) - 2 * ((D.gj 1).natDegree : ℤ) ≤
      2 * (D.W_F : ℤ) - 2 * (wY : ℤ) + 2 := by
  by_cases hR0 : S.R = 0
  · have hq0 : S.q = 0 := S.q_eq_zero_iff.mpr hR0
    have hD2_p : S.D1.natDegree = S.p.natDegree := by
      have hp1_u : IsUnit K.p1 := K.hp1_q1_cop.isUnit_of_dvd' dvd_rfl (by
        have hq10 : K.q1 = 0 := (mul_eq_zero.mp (K.hq_fac.symm.trans hq0)).resolve_left S.D2_ne_zero
        rw [hq10]; exact dvd_zero _)
      have hp1_0 := natDegree_eq_zero_of_isUnit hp1_u
      have := K.natDegree_p_eq; omega
    have h338 := K.row338_bound
    have hg2 := D.natDegree_gj_le 2
    have h5 := D.hWF_lo; have hw := D.hwY_pos
    rw [hR0, natDegree_zero]; omega
  · have hq_ne : S.q ≠ 0 := mt S.q_eq_zero_iff.mp hR0
    have hq1_ne : K.q1 ≠ 0 := fun h0 => hq_ne (by rw [K.hq_fac, h0, mul_zero])
    have hM10_ne : S.M10 ≠ 0 := by
      rw [K.hM10_fac]; exact mul_ne_zero (mul_ne_zero (pow_ne_zero 2 hq1_ne) K.hK1_ne) K.hLam1_ne
    have hq_deg : S.R.natDegree = S.D1.natDegree + K.q1.natDegree := by
      rw [← S.natDegree_q_eq_R, K.hq_fac, natDegree_mul S.D2_ne_zero hq1_ne, ← S.D1_natDegree]
    have hdeg : (S.p * S.M10).natDegree =
        S.p.natDegree + 2 * K.q1.natDegree + K.K1.natDegree + K.Lam1.natDegree := by
      rw [natDegree_mul S.hp hM10_ne, K.hM10_fac,
        natDegree_mul (mul_ne_zero (pow_ne_zero 2 hq1_ne) K.hK1_ne) K.hLam1_ne,
        natDegree_mul (pow_ne_zero 2 hq1_ne) K.hK1_ne, natDegree_pow]; ring
    have h2deg : 2 * (S.p * S.M10).natDegree ≤ D.W_F - wY + (D.gj 1).natDegree := by
      rw [S.p_mul_M10]
      have hB0 := D.two_mul_natDegree_Bj_le 0; have hC0 := D.two_mul_natDegree_Cj_le 0
      have h5 := D.hWF_lo; have hw := D.hwY_pos
      have ht1 : 2 * (D.Cj 1 * D.Bj 0).natDegree ≤ D.W_F - wY + (D.gj 1).natDegree := by
        by_cases hC1 : D.Cj 1 = 0
        · simp [hC1]
        · have := two_mul_natDegree_le_even_odd (D.Cj 1) (D.Bj 1) hC1
          have := natDegree_mul_le (p := D.Cj 1) (q := D.Bj 0)
          unfold KerD45Data.gj at *; omega
      have ht2 : 2 * (D.Cj 0 * D.Bj 1).natDegree ≤ D.W_F - wY + (D.gj 1).natDegree := by
        by_cases hB1 : D.Bj 1 = 0
        · simp [hB1]
        · have := two_mul_natDegree_add_one_le_even_odd (D.Cj 1) (D.Bj 1) hB1
          have := natDegree_mul_le (p := D.Cj 0) (q := D.Bj 1)
          unfold KerD45Data.gj at *; omega
      have hadd := natDegree_add_le (D.Cj 1 * D.Bj 0) (D.Cj 0 * D.Bj 1); omega
    have h5 := D.hWF_lo; have hw := D.hwY_pos; omega

lemma row340_bound :
    5 * (S.R.natDegree : ℤ) + 2 * (K.K1.natDegree : ℤ) + 2 * (K.Lam1.natDegree : ℤ) -
      4 * (S.D1.natDegree : ℤ) ≤ 2 * (D.W_F : ℤ) - 3 * (wY : ℤ) + 1 := by
  by_cases hR0 : S.R = 0
  · have hq0 : S.q = 0 := S.q_eq_zero_iff.mpr hR0
    have hD2_p : S.D1.natDegree = S.p.natDegree := by
      have hp1_u : IsUnit K.p1 := K.hp1_q1_cop.isUnit_of_dvd' dvd_rfl (by
        have hq10 : K.q1 = 0 := (mul_eq_zero.mp (K.hq_fac.symm.trans hq0)).resolve_left S.D2_ne_zero
        rw [hq10]; exact dvd_zero _)
      have hp1_0 := natDegree_eq_zero_of_isUnit hp1_u
      have := K.natDegree_p_eq; omega
    have hM21_ne : S.M21 ≠ 0 := by
      rw [K.hM21_fac]; exact mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero 2 S.D2_ne_zero) (pow_ne_zero 4 K.hp1_ne)) K.hK1_ne) K.hLam1_ne
    have hpM21 := S.natDegree_p_add_M21_le hM21_ne
    have hM21_deg : S.M21.natDegree = 2 * S.D1.natDegree + 4 * K.p1.natDegree + K.K1.natDegree + K.Lam1.natDegree := by
      rw [K.hM21_fac,
        natDegree_mul (mul_ne_zero (mul_ne_zero (pow_ne_zero 2 S.D2_ne_zero) (pow_ne_zero 4 K.hp1_ne)) K.hK1_ne) K.hLam1_ne,
        natDegree_mul (mul_ne_zero (pow_ne_zero 2 S.D2_ne_zero) (pow_ne_zero 4 K.hp1_ne)) K.hK1_ne,
        natDegree_mul (pow_ne_zero 2 S.D2_ne_zero) (pow_ne_zero 4 K.hp1_ne),
        natDegree_pow, natDegree_pow, ← S.D1_natDegree]
    have h5 := D.hWF_lo; have hw := D.hwY_pos
    rw [hR0, natDegree_zero]; omega
  · have hq_ne : S.q ≠ 0 := mt S.q_eq_zero_iff.mp hR0
    have hq1_ne : K.q1 ≠ 0 := fun h0 => hq_ne (by rw [K.hq_fac, h0, mul_zero])
    have hM10_ne : S.M10 ≠ 0 := by
      rw [K.hM10_fac]; exact mul_ne_zero (mul_ne_zero (pow_ne_zero 2 hq1_ne) K.hK1_ne) K.hLam1_ne
    have hq_deg : S.R.natDegree = S.D1.natDegree + K.q1.natDegree := by
      rw [← S.natDegree_q_eq_R, K.hq_fac, natDegree_mul S.D2_ne_zero hq1_ne, ← S.D1_natDegree]
    have hRM10 := S.natDegree_R_mul_M10_le
    rw [natDegree_mul hR0 (mt (comp_X_sq_eq_zero_iff S.M10).mp hM10_ne), natDegree_comp_X_sq,
      K.hM10_fac, natDegree_mul (mul_ne_zero (pow_ne_zero 2 hq1_ne) K.hK1_ne) K.hLam1_ne,
      natDegree_mul (pow_ne_zero 2 hq1_ne) K.hK1_ne, natDegree_pow] at hRM10
    have h5 := D.hWF_lo; have hw := D.hwY_pos; omega

lemma q1_trichotomy :
    (S.H1.natDegree ≤ 8 * S.p.natDegree + D.W_F - wY + 1) ∨
    (S.H1.natDegree ≤ 4 * S.p.natDegree + 2 * S.R.natDegree + (D.gj 1).natDegree) ∨
    (S.H1.natDegree ≤ 4 * S.R.natDegree + (D.gj 2).natDegree) := by
  have h5 := D.hWF_lo; have hw := D.hwY_pos
  have hg0 := D.natDegree_gj_le 0
  have hp_sq : (S.p.comp (X ^ 2)).natDegree = 2 * S.p.natDegree := natDegree_comp_X_sq S.p
  have ht1 : (S.p.comp (X ^ 2) ^ 4 * D.gj 0).natDegree ≤ 8 * S.p.natDegree + D.W_F - wY + 1 :=
    natDegree_mul_le.trans (Nat.add_le_add (natDegree_pow_le.trans (by rw [hp_sq])) hg0) |>.trans (by omega)
  have ht2 : (S.p.comp (X ^ 2) ^ 2 * S.R ^ 2 * D.gj 1).natDegree ≤ 4 * S.p.natDegree + 2 * S.R.natDegree + (D.gj 1).natDegree :=
    natDegree_mul_le.trans (Nat.add_le_add
      (natDegree_mul_le.trans (Nat.add_le_add (natDegree_pow_le.trans (by rw [hp_sq])) natDegree_pow_le)) le_rfl) |>.trans (by omega)
  have ht3 : (S.R ^ 4 * D.gj 2).natDegree ≤ 4 * S.R.natDegree + (D.gj 2).natDegree :=
    natDegree_mul_le.trans (Nat.add_le_add natDegree_pow_le le_rfl)
  have hle : S.H1.natDegree ≤ max (max (8 * S.p.natDegree + D.W_F - wY + 1)
      (4 * S.p.natDegree + 2 * S.R.natDegree + (D.gj 1).natDegree))
      (4 * S.R.natDegree + (D.gj 2).natDegree) := by
    unfold KerD45Syzygy.H1
    exact (natDegree_add_le _ _).trans (max_le_max ((natDegree_add_le _ _).trans (max_le_max ht1 ht2)) ht3)
  rcases le_max_iff.mp hle with h12 | h3
  · rcases le_max_iff.mp h12 with h1 | h2
    · exact Or.inl h1
    · exact Or.inr (Or.inl h2)
  · exact Or.inr (Or.inr h3)

/-! #### Domain polynomials `M_0, N_1, S_hit3, H_rem, Q, S_g2, g2_rem, M_0_eff, S_K, H_K` -/

noncomputable def linProd (s : Finset Idx) : Fld[X] := ∏ i ∈ s, (X - C (BinaryIRSProfile.domain i))

lemma linProd_monic (s : Finset Idx) : (linProd s).Monic :=
  Polynomial.monic_prod_of_monic _ _ fun _ _ => monic_X_sub_C _

lemma linProd_ne (s : Finset Idx) : linProd s ≠ 0 := (linProd_monic s).ne_zero

lemma linProd_natDegree (s : Finset Idx) : (linProd s).natDegree = s.card := by
  unfold linProd; rw [natDegree_prod_of_monic _ _ (fun _ _ => monic_X_sub_C _)]; simp [natDegree_X_sub_C]

open Classical in
lemma linProd_rm (s : Finset Idx) (a : AlgebraicClosure Fld) :
    ((linProd s).map (algebraMap Fld (AlgebraicClosure Fld))).rootMultiplicity a =
      if ∃ i ∈ s, a = algebraMap Fld (AlgebraicClosure Fld) (BinaryIRSProfile.domain i) then 1 else 0 := by
  let ι : Fld →+* AlgebraicClosure Fld := algebraMap Fld (AlgebraicClosure Fld)
  have hmap : (linProd s).map ι = ∏ i ∈ s, (X - C (ι (BinaryIRSProfile.domain i))) := by
    unfold linProd; rw [Polynomial.map_prod]; apply Finset.prod_congr rfl; intro i _; simp
  rw [hmap]; split_ifs with h
  · obtain ⟨i, hi, rfl⟩ := h
    rw [← Finset.mul_prod_erase _ _ hi, rootMultiplicity_mul (mul_ne_zero (X_sub_C_ne_zero _)
      (Finset.prod_ne_zero_iff.mpr fun _ _ => X_sub_C_ne_zero _)), rootMultiplicity_X_sub_C, if_pos rfl]
    have h0 : (∏ j ∈ s.erase i, (X - C (ι (BinaryIRSProfile.domain j)))).rootMultiplicity
        (ι (BinaryIRSProfile.domain i)) = 0 := by
      apply rootMultiplicity_eq_zero_iff.mpr; intro hr; exfalso
      rw [IsRoot, eval_prod, Finset.prod_eq_zero_iff] at hr
      obtain ⟨j, hj, hje⟩ := hr
      rw [eval_sub, eval_X, eval_C, sub_eq_zero] at hje
      exact (Finset.mem_erase.mp hj).1 (BinaryIRSProfile.domain.injective (ι.injective hje)).symm
    rw [h0, add_zero]
  · apply rootMultiplicity_eq_zero_iff.mpr; intro hr; exfalso
    rw [IsRoot, eval_prod, Finset.prod_eq_zero_iff] at hr
    obtain ⟨i, hi, hie⟩ := hr
    rw [eval_sub, eval_X, eval_C, sub_eq_zero] at hie
    exact h ⟨i, hi, hie⟩

omit K in
noncomputable def I_M0 (_K : KerD45KData S) : Finset Idx := by
  classical exact Finset.univ.filter fun i => D.k i = 0 ∨ ¬ S.isU0 i
noncomputable def I_N1 : Finset Idx := by
  classical exact Finset.univ.filter fun i => (D.k i = 1 ∧ S.isU0 i) ∨ (K.isML i ∧ K.isD1 i)
noncomputable def I_hit3 : Finset Idx := by
  classical exact Finset.univ.filter fun i => 2 ≤ D.k i ∧ S.isU0 i ∧ ¬ (K.isML i ∧ K.isD1 i)
noncomputable def I_g2 : Finset Idx := by
  classical exact Finset.univ.filter fun i => 2 ≤ D.k i ∧ S.isU0 i ∧ ¬ K.isMbad i
noncomputable def I_M0eff : Finset Idx := by
  classical exact Finset.univ.filter fun i => D.k i ≤ 1 ∨ ¬ S.isU0 i ∨ K.isMbad i

noncomputable def M0 : Fld[X] := linProd K.I_M0
noncomputable def N1 : Fld[X] := linProd K.I_N1
noncomputable def Shit3 : Fld[X] := linProd K.I_hit3
noncomputable def Sg2 : Fld[X] := linProd K.I_g2
noncomputable def M0eff : Fld[X] := linProd K.I_M0eff

lemma M0_ne : K.M0 ≠ 0 := linProd_ne _
lemma N1_ne : K.N1 ≠ 0 := linProd_ne _
lemma Shit3_ne : K.Shit3 ≠ 0 := linProd_ne _
lemma Sg2_ne : K.Sg2 ≠ 0 := linProd_ne _
lemma M0eff_ne : K.M0eff ≠ 0 := linProd_ne _

lemma card_I_M0 : K.I_M0.card = D.n0 + (D.n1 - S.n1U) + (D.n2 - S.n2U) + (D.n3 - S.n3U) := by
  classical
  have hU := S.U_counts_ineqs
  have hZ : (K.I_M0.card : ℤ) = (D.n0 : ℤ) + ((D.n1 : ℤ) - (S.n1U : ℤ)) +
      ((D.n2 : ℤ) - (S.n2U : ℤ)) + ((D.n3 : ℤ) - (S.n3U : ℤ)) := by
    have h1 : (K.I_M0.card : ℤ) = ∑ i : Idx, (if D.k i = 0 ∨ ¬ S.isU0 i then (1 : ℤ) else 0) := by unfold I_M0; exact card_filter_univ_Z _ _
    have h2 : (D.n0 : ℤ) + ((D.n1 : ℤ) - (S.n1U : ℤ)) + ((D.n2 : ℤ) - (S.n2U : ℤ)) + ((D.n3 : ℤ) - (S.n3U : ℤ)) =
        ∑ i : Idx, ((if D.k i = 0 then (1 : ℤ) else 0) + (if D.k i = 1 then 1 else 0) - (if D.k i = 1 ∧ S.isU0 i then 1 else 0) +
          (if D.k i = 2 then 1 else 0) - (if D.k i = 2 ∧ S.isU0 i then 1 else 0) +
          (if 3 ≤ D.k i then 1 else 0) - (if 3 ≤ D.k i ∧ S.isU0 i then 1 else 0)) := by
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
        ← n0_Z, ← n1_Z, ← n2_Z, ← n3_Z, ← nt_Z, ← n1U_Z, ← n2U_Z, ← n3U_Z,
        ← K.mbadCnt_Z, ← K.mLCnt_Z, ← K.din2Cnt_Z, ← K.din3Cnt_Z, ← K.dmL2Cnt_Z, ← K.dmL3Cnt_Z,
        ← K.d2k1UCnt_Z, ← K.d2k0Cnt_Z, ← K.mu1Cnt_Z, ← K.ntUNorm_Z, ← K.ntUMbad_Z, ← K.ntUML_Z, ← K.muExK3_Z] <;> ring
    rw [h1, h2]; apply Finset.sum_congr rfl; intro i _
    by_cases hU : S.isU0 i <;>
      simp only [hU, ne_eq, not_true_eq_false, not_false_eq_true, and_true, and_false, true_and, false_and, or_true, or_false, ↓reduceIte] <;>
      (try split_ifs) <;> omega
  omega

lemma card_I_N1 : K.I_N1.card = S.n1U + K.dmLCnt := by
  classical
  have hZ : (K.I_N1.card : ℤ) = (S.n1U : ℤ) + (K.dmLCnt : ℤ) := by
    have h1 : (K.I_N1.card : ℤ) = ∑ i : Idx, (if (D.k i = 1 ∧ S.isU0 i) ∨ (K.isML i ∧ K.isD1 i) then (1 : ℤ) else 0) := by unfold I_N1; exact card_filter_univ_Z _ _
    have h2 : (S.n1U : ℤ) + (K.dmLCnt : ℤ) = ∑ i : Idx, ((if D.k i = 1 ∧ S.isU0 i then (1 : ℤ) else 0) +
        (if D.k i = 2 ∧ K.isML i ∧ K.isD1 i then 1 else 0) + (if 3 ≤ D.k i ∧ K.isML i ∧ K.isD1 i then 1 else 0)) := by
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
        ← n0_Z, ← n1_Z, ← n2_Z, ← n3_Z, ← nt_Z, ← n1U_Z, ← n2U_Z, ← n3U_Z,
        ← K.mbadCnt_Z, ← K.mLCnt_Z, ← K.din2Cnt_Z, ← K.din3Cnt_Z, ← K.dmL2Cnt_Z, ← K.dmL3Cnt_Z,
        ← K.d2k1UCnt_Z, ← K.d2k0Cnt_Z, ← K.mu1Cnt_Z, ← K.ntUNorm_Z, ← K.ntUMbad_Z, ← K.ntUML_Z, ← K.muExK3_Z]
      simp only [dmLCnt, Nat.cast_add]; ring
    rw [h1, h2]; apply Finset.sum_congr rfl; intro i _
    by_cases hU : S.isU0 i <;> by_cases hD1 : K.isD1 i <;>
      by_cases hg : K.g2t.eval (BinaryIRSProfile.domain i) = 0 <;>
      by_cases hm : K.M0s.eval (BinaryIRSProfile.domain i ^ 2) = 0 <;>
      simp only [isML, hU, hD1, hg, hm, ne_eq, not_true_eq_false, not_false_eq_true,
        and_true, and_false, true_and, false_and, or_true, or_false, ↓reduceIte] <;>
      (try split_ifs) <;> omega
  omega

lemma card_I_hit3 : K.I_hit3.card = S.n2U + S.n3U - K.dmLCnt := by
  classical
  have hZ : (K.I_hit3.card : ℤ) = (S.n2U : ℤ) + (S.n3U : ℤ) - (K.dmLCnt : ℤ) := by
    have h1 : (K.I_hit3.card : ℤ) = ∑ i : Idx, (if 2 ≤ D.k i ∧ S.isU0 i ∧ ¬ (K.isML i ∧ K.isD1 i) then (1 : ℤ) else 0) := by unfold I_hit3; exact card_filter_univ_Z _ _
    have h2 : (S.n2U : ℤ) + (S.n3U : ℤ) - (K.dmLCnt : ℤ) =
        ∑ i : Idx, ((if D.k i = 2 ∧ S.isU0 i then (1 : ℤ) else 0) + (if 3 ≤ D.k i ∧ S.isU0 i then 1 else 0) -
          (if D.k i = 2 ∧ K.isML i ∧ K.isD1 i then 1 else 0) - (if 3 ≤ D.k i ∧ K.isML i ∧ K.isD1 i then 1 else 0)) := by
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
        ← n0_Z, ← n1_Z, ← n2_Z, ← n3_Z, ← nt_Z, ← n1U_Z, ← n2U_Z, ← n3U_Z,
        ← K.mbadCnt_Z, ← K.mLCnt_Z, ← K.din2Cnt_Z, ← K.din3Cnt_Z, ← K.dmL2Cnt_Z, ← K.dmL3Cnt_Z,
        ← K.d2k1UCnt_Z, ← K.d2k0Cnt_Z, ← K.mu1Cnt_Z, ← K.ntUNorm_Z, ← K.ntUMbad_Z, ← K.ntUML_Z, ← K.muExK3_Z]
      simp only [dmLCnt, Nat.cast_add]; ring
    rw [h1, h2]; apply Finset.sum_congr rfl; intro i _
    by_cases hU : S.isU0 i <;> by_cases hD1 : K.isD1 i <;>
      by_cases hg : K.g2t.eval (BinaryIRSProfile.domain i) = 0 <;>
      by_cases hm : K.M0s.eval (BinaryIRSProfile.domain i ^ 2) = 0 <;>
      simp only [isML, hU, hD1, hg, hm, ne_eq, not_true_eq_false, not_false_eq_true,
        and_true, and_false, true_and, false_and, ↓reduceIte] <;>
      (try split_ifs) <;> omega
  omega

lemma card_I_g2 : K.I_g2.card = S.n2U + S.n3U - K.mbadCnt := by
  classical
  have hZ : (K.I_g2.card : ℤ) = (S.n2U : ℤ) + (S.n3U : ℤ) - (K.mbadCnt : ℤ) := by
    have h1 : (K.I_g2.card : ℤ) = ∑ i : Idx, (if 2 ≤ D.k i ∧ S.isU0 i ∧ ¬ K.isMbad i then (1 : ℤ) else 0) := by unfold I_g2; exact card_filter_univ_Z _ _
    have h2 : (S.n2U : ℤ) + (S.n3U : ℤ) - (K.mbadCnt : ℤ) =
        ∑ i : Idx, ((if D.k i = 2 ∧ S.isU0 i then (1 : ℤ) else 0) + (if 3 ≤ D.k i ∧ S.isU0 i then 1 else 0) -
          (if K.isMbad i then 1 else 0)) := by
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
        ← n0_Z, ← n1_Z, ← n2_Z, ← n3_Z, ← nt_Z, ← n1U_Z, ← n2U_Z, ← n3U_Z,
        ← K.mbadCnt_Z, ← K.mLCnt_Z, ← K.din2Cnt_Z, ← K.din3Cnt_Z, ← K.dmL2Cnt_Z, ← K.dmL3Cnt_Z,
        ← K.d2k1UCnt_Z, ← K.d2k0Cnt_Z, ← K.mu1Cnt_Z, ← K.ntUNorm_Z, ← K.ntUMbad_Z, ← K.ntUML_Z, ← K.muExK3_Z] <;> ring
    rw [h1, h2]; apply Finset.sum_congr rfl; intro i _
    by_cases hU : S.isU0 i <;> by_cases hg : K.g2t.eval (BinaryIRSProfile.domain i) = 0 <;>
      simp only [isMbad, hU, hg, ne_eq, not_true_eq_false, not_false_eq_true,
        and_true, and_false, true_and, false_and, ↓reduceIte] <;>
      (try split_ifs) <;> omega
  omega

lemma card_I_M0eff : K.I_M0eff.card = D.n0 + D.n1 + (D.n2 - S.n2U) + (D.n3 - S.n3U) + K.mbadCnt := by
  classical
  have hU := S.U_counts_ineqs
  have hZ : (K.I_M0eff.card : ℤ) = (D.n0 : ℤ) + (D.n1 : ℤ) + ((D.n2 : ℤ) - (S.n2U : ℤ)) +
      ((D.n3 : ℤ) - (S.n3U : ℤ)) + (K.mbadCnt : ℤ) := by
    have h1 : (K.I_M0eff.card : ℤ) = ∑ i : Idx, (if D.k i ≤ 1 ∨ ¬ S.isU0 i ∨ K.isMbad i then (1 : ℤ) else 0) := by unfold I_M0eff; exact card_filter_univ_Z _ _
    have h2 : (D.n0 : ℤ) + (D.n1 : ℤ) + ((D.n2 : ℤ) - (S.n2U : ℤ)) + ((D.n3 : ℤ) - (S.n3U : ℤ)) + (K.mbadCnt : ℤ) =
        ∑ i : Idx, ((if D.k i = 0 then (1 : ℤ) else 0) + (if D.k i = 1 then 1 else 0) +
          (if D.k i = 2 then 1 else 0) - (if D.k i = 2 ∧ S.isU0 i then 1 else 0) +
          (if 3 ≤ D.k i then 1 else 0) - (if 3 ≤ D.k i ∧ S.isU0 i then 1 else 0) +
          (if K.isMbad i then 1 else 0)) := by
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
        ← n0_Z, ← n1_Z, ← n2_Z, ← n3_Z, ← nt_Z, ← n1U_Z, ← n2U_Z, ← n3U_Z,
        ← K.mbadCnt_Z, ← K.mLCnt_Z, ← K.din2Cnt_Z, ← K.din3Cnt_Z, ← K.dmL2Cnt_Z, ← K.dmL3Cnt_Z,
        ← K.d2k1UCnt_Z, ← K.d2k0Cnt_Z, ← K.mu1Cnt_Z, ← K.ntUNorm_Z, ← K.ntUMbad_Z, ← K.ntUML_Z, ← K.muExK3_Z] <;> ring
    rw [h1, h2]; apply Finset.sum_congr rfl; intro i _
    by_cases hU : S.isU0 i <;> by_cases hg : K.g2t.eval (BinaryIRSProfile.domain i) = 0 <;>
      simp only [isMbad, hU, hg, ne_eq, not_true_eq_false, not_false_eq_true,
        and_true, and_false, true_and, false_and, or_true, or_false, ↓reduceIte] <;>
      (try split_ifs) <;> omega
  omega

lemma Ndom_eq_M0_N1_Shit3 : Ndom = K.M0 * K.N1 * K.Shit3 := by
  classical
  have hd1 : Disjoint K.I_M0 K.I_N1 := Finset.disjoint_filter.mpr fun i _ h1 h2 => by
    unfold isML at h2; rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> first | omega | exact h1 h2.2 | exact h1 h2.1.2.1
  have hd2 : Disjoint (K.I_M0 ∪ K.I_N1) K.I_hit3 := Finset.disjoint_left.mpr fun i h1 h2 => by
    simp only [I_M0, I_N1, I_hit3, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
    rcases h1 with (h1 | h1) | (h1 | h1)
    · omega
    · exact h1 h2.2.1
    · omega
    · exact h2.2.2 h1
  have hun : K.I_M0 ∪ K.I_N1 ∪ K.I_hit3 = Finset.univ := by
    ext i; simp only [I_M0, I_N1, I_hit3, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
    by_cases hU : S.isU0 i
    · by_cases hk0 : D.k i = 0
      · left; left; left; exact hk0
      · by_cases hk1 : D.k i = 1
        · left; right; left; exact ⟨hk1, hU⟩
        · by_cases hm : K.isML i ∧ K.isD1 i
          · left; right; right; exact hm
          · right; exact ⟨by omega, hU, hm⟩
    · left; left; right; exact hU
  unfold Ndom M0 N1 Shit3 linProd
  rw [← Finset.prod_union hd1, ← Finset.prod_union hd2, hun]

lemma Ndom_eq_M0eff_Sg2 : Ndom = K.M0eff * K.Sg2 := by
  classical
  have hd : Disjoint K.I_M0eff K.I_g2 := Finset.disjoint_filter.mpr fun i _ h1 h2 => by
    rcases h1 with h1 | h1 | h1
    · omega
    · exact h1 h2.2.1
    · exact h2.2.2 h1
  have hun : K.I_M0eff ∪ K.I_g2 = Finset.univ := by
    ext i; simp only [I_M0eff, I_g2, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
    by_cases hU : S.isU0 i
    · by_cases hk1 : D.k i ≤ 1
      · left; left; exact hk1
      · by_cases hmb : K.isMbad i
        · left; right; right; exact hmb
        · right; exact ⟨by omega, hU, hmb⟩
    · left; right; left; exact hU
  unfold Ndom M0eff Sg2 linProd
  rw [← Finset.prod_union hd, hun]

lemma Sg2_dvd_g2t : K.Sg2 ∣ K.g2t := by
  classical
  unfold Sg2 linProd
  have hpw : Pairwise fun i j : Idx => IsCoprime (X - C (BinaryIRSProfile.domain i)) (X - C (BinaryIRSProfile.domain j)) :=
    fun i j hij => (Polynomial.irreducible_X_sub_C _).coprime_iff_not_dvd.mpr fun hd => by
      have h0 := dvd_iff_isRoot.mp hd; simp [IsRoot] at h0
      exact hij (BinaryIRSProfile.domain.injective (sub_eq_zero.mp h0))
  apply Finset.prod_dvd_of_coprime (fun i _ j _ hij => hpw hij)
  intro i hi
  unfold I_g2 at hi; rw [Finset.mem_filter] at hi; rcases hi with ⟨_, hi⟩
  unfold isMbad at hi
  apply dvd_iff_isRoot.mpr; by_contra hne; exact hi.2.2 ⟨hi.1, hi.2.1, hne⟩

lemma N1_Shit3_cube_dvd_Hraw : K.N1 * K.Shit3 ^ 3 ∣ K.M0s.comp (X ^ 2) * K.g2t := by
  classical
  have hdisj : Disjoint K.I_N1 K.I_hit3 := Finset.disjoint_filter.mpr fun i _ h1 h2 => by
    rcases h1 with ⟨hk1, _⟩ | h1
    · have := h2.1; omega
    · exact h2.2.2 h1
  have hpw : Pairwise fun i j : Idx => IsCoprime (X - C (BinaryIRSProfile.domain i)) (X - C (BinaryIRSProfile.domain j)) :=
    fun i j hij => (Polynomial.irreducible_X_sub_C _).coprime_iff_not_dvd.mpr fun hd => by
      have h0 := dvd_iff_isRoot.mp hd; simp [IsRoot] at h0
      exact hij (BinaryIRSProfile.domain.injective (sub_eq_zero.mp h0))
  have hcop : IsCoprime K.N1 (K.Shit3 ^ 3) := by
    apply IsCoprime.pow_right; unfold N1 Shit3 linProd
    exact IsCoprime.prod_left fun i hi => IsCoprime.prod_right fun j hj =>
      hpw (fun heq => by subst heq; exact Finset.disjoint_left.mp hdisj hi hj)
  apply hcop.mul_dvd
  · unfold N1 linProd
    apply Finset.prod_dvd_of_coprime (fun i _ j _ hij => hpw hij)
    intro i hi
    unfold I_N1 at hi; rw [Finset.mem_filter] at hi; rcases hi with ⟨_, hi⟩
    rcases hi with ⟨hk1, hU⟩ | ⟨hmL, _⟩
    · by_cases hD1 : K.isD1 i
      · exact dvd_mul_of_dvd_right (dvd_iff_isRoot.mpr (K.g2t_zero_of_D1_zero hD1)) _
      · have hH1d : X - C (BinaryIRSProfile.domain i) ∣ S.H1 := by
          have := S.pow_dvd_H1_of_isU0 i hU; rwa [hk1, pow_one] at this
        rw [K.hH1_fac, mul_assoc] at hH1d
        have hcopD : IsCoprime (X - C (BinaryIRSProfile.domain i)) (S.D1 ^ 4) :=
          ((Polynomial.irreducible_X_sub_C _).coprime_iff_not_dvd.mpr (mt dvd_iff_isRoot.mp hD1)).pow_right
        exact hcopD.dvd_of_dvd_mul_left hH1d
    · exact dvd_mul_of_dvd_right (dvd_iff_isRoot.mpr hmL.2.2.1) _
  · unfold Shit3 linProd; rw [← Finset.prod_pow]
    apply Finset.prod_dvd_of_coprime (fun i _ j _ hij => (hpw hij).pow)
    intro i hi
    unfold I_hit3 at hi; rw [Finset.mem_filter] at hi; rcases hi with ⟨_, hi⟩
    by_cases hD1 : K.isD1 i
    · have hg0 := K.g2t_zero_of_D1_zero hD1
      have hM0 : K.M0s.eval (BinaryIRSProfile.domain i ^ 2) = 0 := by
        by_contra hne; exact hi.2.2 ⟨⟨hi.1, hi.2.1, hg0, hne⟩, hD1⟩
      rw [show (3 : ℕ) = 2 + 1 by rfl, pow_add, pow_one]
      exact mul_dvd_mul ((pow_dvd_comp_X_sq_iff K.M0s (BinaryIRSProfile.domain i) 1).mpr (by rw [pow_one]; exact dvd_iff_isRoot.mpr hM0))
        (dvd_iff_isRoot.mpr hg0)
    · have hH1d := (pow_dvd_pow (X - C (BinaryIRSProfile.domain i)) (by have := hi.1; omega : 3 ≤ 2 * D.k i - 1)).trans
        (S.pow_dvd_H1_of_isU0 i hi.2.1)
      rw [K.hH1_fac, mul_assoc] at hH1d
      have hcopD : IsCoprime ((X - C (BinaryIRSProfile.domain i)) ^ 3) (S.D1 ^ 4) :=
        (((Polynomial.irreducible_X_sub_C _).coprime_iff_not_dvd.mpr (mt dvd_iff_isRoot.mp hD1)).pow_left).pow_right
      exact hcopD.dvd_of_dvd_mul_left hH1d

end KerD45KData
end B6402Table4K
end ProximityPrize.SubmissionBinaryLower
