import ProximityPrize.SubmissionBinaryLower.Binary6402Table4KPart1
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

lemma g2t_extra_le :
    (S.n2U + S.n3U - K.mbadCnt) + K.d2k0Cnt + (S.n1U - K.mu1Cnt) + 2 * (K.mLCnt - K.dmLCnt) ≤ K.g2t.natDegree := by
  classical
  let f : Idx → ℕ := fun i =>
    if K.isNorm i then 1
    else if K.isML i then (if K.isD1 i then 1 else 3)
    else if D.k i = 0 ∧ K.isD1 i then 1
    else if D.k i = 1 ∧ S.isU0 i ∧ (K.isD1 i ∨ K.M0s.eval (BinaryIRSProfile.domain i ^ 2) ≠ 0) then 1
    else 0
  have hdvd : ∀ i ∈ (Finset.univ : Finset Idx), (X - C (BinaryIRSProfile.domain i)) ^ f i ∣ K.g2t := fun i _ => by
    dsimp [f]; split_ifs with hn hmL hD1 hk0 hk1
    · rw [pow_one]; exact dvd_iff_isRoot.mpr hn.2.2.1
    · rw [pow_one]; exact dvd_iff_isRoot.mpr hmL.2.2.1
    · have hH1d := (pow_dvd_pow (X - C (BinaryIRSProfile.domain i)) (by have := hmL.1; omega : 3 ≤ 2 * D.k i - 1)).trans
        (S.pow_dvd_H1_of_isU0 i hmL.2.1)
      rw [K.hH1_fac] at hH1d
      have hcop : IsCoprime ((X - C (BinaryIRSProfile.domain i)) ^ 3) (S.D1 ^ 4 * K.M0s.comp (X ^ 2)) := by
        apply IsCoprime.pow_left
        have hne : (S.D1 ^ 4 * K.M0s.comp (X ^ 2)).eval (BinaryIRSProfile.domain i) ≠ 0 := by
          rw [eval_mul, eval_pow, eval_comp, eval_pow, eval_X]
          exact mul_ne_zero (pow_ne_zero 4 hD1) hmL.2.2.2
        exact (Polynomial.irreducible_X_sub_C _).coprime_iff_not_dvd.mpr (mt dvd_iff_isRoot.mp hne)
      exact hcop.dvd_of_dvd_mul_left hH1d
    · rw [pow_one]; exact dvd_iff_isRoot.mpr (K.g2t_zero_of_D1_zero hk0.2)
    · rcases hk1.2.2 with hD1' | hM0'
      · rw [pow_one]; exact dvd_iff_isRoot.mpr (K.g2t_zero_of_D1_zero hD1')
      · by_cases hD1' : K.isD1 i
        · rw [pow_one]; exact dvd_iff_isRoot.mpr (K.g2t_zero_of_D1_zero hD1')
        · have hH1d : X - C (BinaryIRSProfile.domain i) ∣ S.H1 := by
            have := S.pow_dvd_H1_of_isU0 i hk1.2.1; rwa [hk1.1, pow_one] at this
          rw [K.hH1_fac] at hH1d
          have hcop : IsCoprime (X - C (BinaryIRSProfile.domain i)) (S.D1 ^ 4 * K.M0s.comp (X ^ 2)) := by
            have hne : (S.D1 ^ 4 * K.M0s.comp (X ^ 2)).eval (BinaryIRSProfile.domain i) ≠ 0 := by
              rw [eval_mul, eval_pow, eval_comp, eval_pow, eval_X]
              exact mul_ne_zero (pow_ne_zero 4 hD1') hM0'
            exact (Polynomial.irreducible_X_sub_C _).coprime_iff_not_dvd.mpr (mt dvd_iff_isRoot.mp hne)
          rw [pow_one]; exact hcop.dvd_of_dvd_mul_left hH1d
    · simp
  have hle := sum_ord_le_natDegree_of_dvd Finset.univ BinaryIRSProfile.domain BinaryIRSProfile.domain.injective
    K.g2t K.hg2t_ne f hdvd
  have hmb_le : K.mbadCnt ≤ S.n2U + S.n3U := by
    have hZ : (K.mbadCnt : ℤ) ≤ (S.n2U : ℤ) + (S.n3U : ℤ) := by
      have h1 : (K.mbadCnt : ℤ) = ∑ i : Idx, (if K.isMbad i then (1 : ℤ) else 0) := K.mbadCnt_Z
      have h2 : (S.n2U : ℤ) + (S.n3U : ℤ) = ∑ i : Idx, ((if D.k i = 2 ∧ S.isU0 i then (1 : ℤ) else 0) + (if 3 ≤ D.k i ∧ S.isU0 i then 1 else 0)) := by
        rw [Finset.sum_add_distrib, ← n2U_Z, ← n3U_Z]
      rw [h1, h2]; apply Finset.sum_le_sum; intro i _
      by_cases hU : S.isU0 i <;> by_cases hg : K.g2t.eval (BinaryIRSProfile.domain i) = 0 <;>
        simp only [isMbad, hU, hg, ne_eq, not_true_eq_false, not_false_eq_true, and_true, and_false, true_and, false_and, ↓reduceIte] <;>
        (try split_ifs) <;> omega
    omega
  have hmu1_le : K.mu1Cnt ≤ S.n1U := by
    have hZ : (K.mu1Cnt : ℤ) ≤ (S.n1U : ℤ) := by
      rw [K.mu1Cnt_Z, n1U_Z]
      apply Finset.sum_le_sum; intro i _
      by_cases hU : S.isU0 i <;> by_cases hD1 : K.isD1 i <;>
        by_cases hm : K.M0s.eval (BinaryIRSProfile.domain i ^ 2) = 0 <;>
        simp only [hU, hD1, hm, ne_eq, not_true_eq_false, not_false_eq_true, and_true, and_false, true_and, false_and, ↓reduceIte] <;>
        (try split_ifs) <;> omega
    omega
  have hdmL_le : K.dmLCnt ≤ K.mLCnt := by
    have hZ : (K.dmLCnt : ℤ) ≤ (K.mLCnt : ℤ) := by
      have h1 : (K.dmLCnt : ℤ) = ∑ i : Idx, ((if D.k i = 2 ∧ K.isML i ∧ K.isD1 i then (1 : ℤ) else 0) +
          (if 3 ≤ D.k i ∧ K.isML i ∧ K.isD1 i then 1 else 0)) := by
        rw [Finset.sum_add_distrib, ← K.dmL2Cnt_Z, ← K.dmL3Cnt_Z]; unfold dmLCnt; push_cast; rfl
      have h2 : (K.mLCnt : ℤ) = ∑ i : Idx, (if K.isML i then (1 : ℤ) else 0) := K.mLCnt_Z
      rw [h1, h2]; apply Finset.sum_le_sum; intro i _
      by_cases hU : S.isU0 i <;> by_cases hD1 : K.isD1 i <;>
        by_cases hg : K.g2t.eval (BinaryIRSProfile.domain i) = 0 <;>
        by_cases hm : K.M0s.eval (BinaryIRSProfile.domain i ^ 2) = 0 <;>
        simp only [isML, hU, hD1, hg, hm, ne_eq, not_true_eq_false, not_false_eq_true, and_true, and_false, true_and, false_and, ↓reduceIte] <;>
        (try split_ifs) <;> omega
    omega
  have hZ : ((S.n2U + S.n3U - K.mbadCnt) + K.d2k0Cnt + (S.n1U - K.mu1Cnt) + 2 * (K.mLCnt - K.dmLCnt) : ℤ) =
      ∑ i : Idx, (f i : ℤ) := by
    have hrew : ((S.n2U : ℤ) + (S.n3U : ℤ) - (K.mbadCnt : ℤ)) + (K.d2k0Cnt : ℤ) +
        ((S.n1U : ℤ) - (K.mu1Cnt : ℤ)) + 2 * ((K.mLCnt : ℤ) - (K.dmLCnt : ℤ)) =
        ∑ i : Idx, ((if D.k i = 2 ∧ S.isU0 i then (1 : ℤ) else 0) + (if 3 ≤ D.k i ∧ S.isU0 i then 1 else 0) -
          (if K.isMbad i then 1 else 0) + (if D.k i = 0 ∧ K.isD1 i then 1 else 0) +
          (if D.k i = 1 ∧ S.isU0 i then 1 else 0) -
          (if D.k i = 1 ∧ S.isU0 i ∧ ¬ K.isD1 i ∧ K.M0s.eval (BinaryIRSProfile.domain i ^ 2) = 0 then 1 else 0) +
          2 * (if K.isML i then 1 else 0) -
          2 * (if D.k i = 2 ∧ K.isML i ∧ K.isD1 i then 1 else 0) -
          2 * (if 3 ≤ D.k i ∧ K.isML i ∧ K.isD1 i then 1 else 0)) := by
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
        ← n0_Z, ← n1_Z, ← n2_Z, ← n3_Z, ← nt_Z, ← n1U_Z, ← n2U_Z, ← n3U_Z,
        ← K.mbadCnt_Z, ← K.mLCnt_Z, ← K.din2Cnt_Z, ← K.din3Cnt_Z, ← K.dmL2Cnt_Z, ← K.dmL3Cnt_Z,
        ← K.d2k1UCnt_Z, ← K.d2k0Cnt_Z, ← K.mu1Cnt_Z, ← K.ntUNorm_Z, ← K.ntUMbad_Z, ← K.ntUML_Z, ← K.muExK3_Z]
      simp only [dmLCnt, Nat.cast_add]; ring
    rw [show ((S.n2U + S.n3U - K.mbadCnt) + K.d2k0Cnt + (S.n1U - K.mu1Cnt) + 2 * (K.mLCnt - K.dmLCnt) : ℤ) =
        ((S.n2U : ℤ) + (S.n3U : ℤ) - (K.mbadCnt : ℤ)) + (K.d2k0Cnt : ℤ) +
        ((S.n1U : ℤ) - (K.mu1Cnt : ℤ)) + 2 * ((K.mLCnt : ℤ) - (K.dmLCnt : ℤ)) by omega, hrew]
    apply Finset.sum_congr rfl; intro i _
    dsimp [f]
    by_cases hU : S.isU0 i <;> by_cases hD1 : K.isD1 i <;>
      by_cases hg : K.g2t.eval (BinaryIRSProfile.domain i) = 0 <;>
      by_cases hm : K.M0s.eval (BinaryIRSProfile.domain i ^ 2) = 0 <;>
      simp only [isNorm, isML, isMbad, hU, hD1, hg, hm, ne_eq, not_true_eq_false, not_false_eq_true,
        and_true, and_false, true_and, false_and, or_true, or_false, true_or, false_or, ↓reduceIte] <;>
      (try split_ifs) <;> omega
  rw [← Nat.cast_sum] at hZ; omega

lemma D1_counts_le : K.dinCnt + K.d2k1UCnt + K.d2k0Cnt + K.dmLCnt ≤ S.D1.natDegree := by
  classical
  let f : Idx → ℕ := fun i => if K.isD1 i then 1 else 0
  have hdvd : ∀ i ∈ (Finset.univ : Finset Idx), (X - C (BinaryIRSProfile.domain i)) ^ f i ∣ S.D1 := fun i _ => by
    dsimp [f]; split_ifs with h
    · rw [pow_one]; exact dvd_iff_isRoot.mpr h
    · simp
  have hle := sum_ord_le_natDegree_of_dvd Finset.univ BinaryIRSProfile.domain BinaryIRSProfile.domain.injective
    S.D1 S.D1_ne_zero f hdvd
  have hsum : K.dinCnt + K.d2k1UCnt + K.d2k0Cnt + K.dmLCnt ≤ ∑ i : Idx, f i := by
    have hZ : (K.dinCnt : ℤ) + (K.d2k1UCnt : ℤ) + (K.d2k0Cnt : ℤ) + (K.dmLCnt : ℤ) ≤ ∑ i : Idx, (f i : ℤ) := by
      have hrew : (K.dinCnt : ℤ) + (K.d2k1UCnt : ℤ) + (K.d2k0Cnt : ℤ) + (K.dmLCnt : ℤ) =
          ∑ i : Idx, ((if D.k i = 2 ∧ K.isNorm i ∧ K.isD1 i then (1 : ℤ) else 0) +
            (if 3 ≤ D.k i ∧ K.isNorm i ∧ K.isD1 i then 1 else 0) +
            (if D.k i = 1 ∧ S.isU0 i ∧ K.isD1 i then 1 else 0) +
            (if D.k i = 0 ∧ K.isD1 i then 1 else 0) +
            (if D.k i = 2 ∧ K.isML i ∧ K.isD1 i then 1 else 0) +
            (if 3 ≤ D.k i ∧ K.isML i ∧ K.isD1 i then 1 else 0)) := by
        simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
        ← n0_Z, ← n1_Z, ← n2_Z, ← n3_Z, ← nt_Z, ← n1U_Z, ← n2U_Z, ← n3U_Z,
        ← K.mbadCnt_Z, ← K.mLCnt_Z, ← K.din2Cnt_Z, ← K.din3Cnt_Z, ← K.dmL2Cnt_Z, ← K.dmL3Cnt_Z,
        ← K.d2k1UCnt_Z, ← K.d2k0Cnt_Z, ← K.mu1Cnt_Z, ← K.ntUNorm_Z, ← K.ntUMbad_Z, ← K.ntUML_Z, ← K.muExK3_Z]
        simp only [dinCnt, dmLCnt, Nat.cast_add]; ring
      rw [hrew]; apply Finset.sum_le_sum; intro i _; dsimp [f]
      by_cases hU : S.isU0 i <;> by_cases hD1 : K.isD1 i <;>
        by_cases hg : K.g2t.eval (BinaryIRSProfile.domain i) = 0 <;>
        by_cases hm : K.M0s.eval (BinaryIRSProfile.domain i ^ 2) = 0 <;>
        simp only [isNorm, isML, hU, hD1, hg, hm, ne_eq, not_true_eq_false, not_false_eq_true,
          and_true, and_false, true_and, false_and, ↓reduceIte] <;>
        (try split_ifs) <;> omega
    rw [← Nat.cast_sum] at hZ; omega
  omega

lemma mL_ntUML_le_Lam1 : K.mLCnt + 2 * K.ntUML ≤ K.Lam1.natDegree := by
  classical
  let f : Idx → ℕ := fun i => if K.isML i then 2 * D.k i - 3 else 0
  have hdvd : ∀ i ∈ (Finset.univ : Finset Idx), (X - C (BinaryIRSProfile.domain i ^ 2)) ^ f i ∣ K.Lam1 := fun i _ => by
    dsimp [f]; split_ifs with hmL
    · have hprod := K.pow_dvd_Lam1_mul_M0s i
      simp only [hmL.2.1, show ¬ D.k i ≤ 1 by have := hmL.1; omega, ↓reduceIte] at hprod
      have hcop := ((Polynomial.irreducible_X_sub_C (BinaryIRSProfile.domain i ^ 2)).coprime_iff_not_dvd.mpr
        (mt dvd_iff_isRoot.mp hmL.2.2.2)).pow_left (m := 2 * D.k i - 3)
      exact hcop.dvd_of_dvd_mul_right hprod
    · simp
  have hle := sum_ord_le_natDegree_of_dvd Finset.univ (fun i => BinaryIRSProfile.domain i ^ 2)
    domain_sq_injective K.Lam1 K.hLam1_ne f hdvd
  have hsum : K.mLCnt + 2 * K.ntUML ≤ ∑ i : Idx, f i := by
    have hZ : (K.mLCnt : ℤ) + 2 * (K.ntUML : ℤ) ≤ ∑ i : Idx, (f i : ℤ) := by
      have hrew : (K.mLCnt : ℤ) + 2 * (K.ntUML : ℤ) =
          ∑ i : Idx, ((if K.isML i then (1 : ℤ) else 0) + 2 * (if K.isML i then ((D.k i - 3 : ℕ) : ℤ) else 0)) := by
        simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
        ← n0_Z, ← n1_Z, ← n2_Z, ← n3_Z, ← nt_Z, ← n1U_Z, ← n2U_Z, ← n3U_Z,
        ← K.mbadCnt_Z, ← K.mLCnt_Z, ← K.din2Cnt_Z, ← K.din3Cnt_Z, ← K.dmL2Cnt_Z, ← K.dmL3Cnt_Z,
        ← K.d2k1UCnt_Z, ← K.d2k0Cnt_Z, ← K.mu1Cnt_Z, ← K.ntUNorm_Z, ← K.ntUMbad_Z, ← K.ntUML_Z, ← K.muExK3_Z]
      rw [hrew]; apply Finset.sum_le_sum; intro i _; dsimp [f]
      by_cases hmL : K.isML i
      · have := hmL.1; simp only [hmL, ↓reduceIte]; omega
      · simp only [hmL, ↓reduceIte]; omega
    rw [← Nat.cast_sum] at hZ; omega
  omega

lemma row321_bound :
    2 * (S.n3U : ℤ) - 2 * (K.dinCnt : ℤ) - 2 * (K.dmLCnt : ℤ) - (K.mbadCnt : ℤ) +
      2 * (K.ntUNorm : ℤ) + 2 * (K.ntUML : ℤ) ≤ (K.Lam1.natDegree : ℤ) + (K.muExK3 : ℤ) := by
  classical
  have hsum_lam : ∑ i : Idx, K.Lam1.rootMultiplicity (BinaryIRSProfile.domain i ^ 2) ≤ K.Lam1.natDegree :=
    sum_ord_le_natDegree_of_dvd Finset.univ (fun i => BinaryIRSProfile.domain i ^ 2)
      domain_sq_injective K.Lam1 K.hLam1_ne _ (fun i _ => pow_rootMultiplicity_dvd K.Lam1 _)
  have hZ : (2 * (S.n3U : ℤ) - 2 * (K.dinCnt : ℤ) - 2 * (K.dmLCnt : ℤ) - (K.mbadCnt : ℤ) +
      2 * (K.ntUNorm : ℤ) + 2 * (K.ntUML : ℤ)) ≤
      ∑ i : Idx, ((K.Lam1.rootMultiplicity (BinaryIRSProfile.domain i ^ 2) : ℤ) +
        ((if 3 ≤ D.k i ∧ K.isNorm i then K.M0s.rootMultiplicity (BinaryIRSProfile.domain i ^ 2) - 1
          else if 3 ≤ D.k i ∧ K.isMbad i then K.M0s.rootMultiplicity (BinaryIRSProfile.domain i ^ 2) - 2 else 0 : ℕ) : ℤ)) := by
    have hrew : 2 * (S.n3U : ℤ) - 2 * (K.dinCnt : ℤ) - 2 * (K.dmLCnt : ℤ) - (K.mbadCnt : ℤ) +
        2 * (K.ntUNorm : ℤ) + 2 * (K.ntUML : ℤ) =
        ∑ i : Idx, (2 * (if 3 ≤ D.k i ∧ S.isU0 i then (1 : ℤ) else 0) -
          2 * (if D.k i = 2 ∧ K.isNorm i ∧ K.isD1 i then 1 else 0) -
          2 * (if 3 ≤ D.k i ∧ K.isNorm i ∧ K.isD1 i then 1 else 0) -
          2 * (if D.k i = 2 ∧ K.isML i ∧ K.isD1 i then 1 else 0) -
          2 * (if 3 ≤ D.k i ∧ K.isML i ∧ K.isD1 i then 1 else 0) -
          (if K.isMbad i then 1 else 0) +
          2 * (if K.isNorm i then ((D.k i - 3 : ℕ) : ℤ) else 0) +
          2 * (if K.isML i then ((D.k i - 3 : ℕ) : ℤ) else 0)) := by
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
        ← n0_Z, ← n1_Z, ← n2_Z, ← n3_Z, ← nt_Z, ← n1U_Z, ← n2U_Z, ← n3U_Z,
        ← K.mbadCnt_Z, ← K.mLCnt_Z, ← K.din2Cnt_Z, ← K.din3Cnt_Z, ← K.dmL2Cnt_Z, ← K.dmL3Cnt_Z,
        ← K.d2k1UCnt_Z, ← K.d2k0Cnt_Z, ← K.mu1Cnt_Z, ← K.ntUNorm_Z, ← K.ntUMbad_Z, ← K.ntUML_Z, ← K.muExK3_Z]
      simp only [dinCnt, dmLCnt, Nat.cast_add]; ring
    rw [hrew]; apply Finset.sum_le_sum; intro i _
    have hprod_rm : (if S.isU0 i then (if D.k i ≤ 1 then 0 else 2 * D.k i - 3) else 0) ≤
        K.Lam1.rootMultiplicity (BinaryIRSProfile.domain i ^ 2) +
          K.M0s.rootMultiplicity (BinaryIRSProfile.domain i ^ 2) := by
      by_cases hU : S.isU0 i
      · have hprod := K.pow_dvd_Lam1_mul_M0s i
        simp only [hU, ↓reduceIte] at hprod ⊢
        have hle := (le_rootMultiplicity_iff (mul_ne_zero K.hLam1_ne K.hM0s_ne)).mpr hprod
        rwa [rootMultiplicity_mul (mul_ne_zero K.hLam1_ne K.hM0s_ne)] at hle
      · simp [hU]
    by_cases hk3 : 3 ≤ D.k i
    · by_cases hU : S.isU0 i
      · by_cases hn : K.isNorm i
        · have hM1 : 1 ≤ K.M0s.rootMultiplicity (BinaryIRSProfile.domain i ^ 2) :=
            (le_rootMultiplicity_iff K.hM0s_ne).mpr (by rw [pow_one]; exact dvd_iff_isRoot.mpr hn.2.2.2)
          have hg := hn.2.2.1; have hm := hn.2.2.2
          by_cases hD1 : K.isD1 i <;>
            simp only [hn, isNorm, isML, isMbad, hU, hD1, hg, hm, ne_eq, not_true_eq_false, not_false_eq_true,
              and_true, and_false, true_and, false_and, ↓reduceIte] at hprod_rm ⊢ <;>
            (try split_ifs at hprod_rm ⊢) <;> omega
        · by_cases hmL : K.isML i
          · have hM0 : K.M0s.rootMultiplicity (BinaryIRSProfile.domain i ^ 2) = 0 :=
              rootMultiplicity_eq_zero_iff.mpr (fun hr => absurd hr hmL.2.2.2)
            have hg := hmL.2.2.1; have hm : ¬ (K.M0s.eval (BinaryIRSProfile.domain i ^ 2) = 0) := hmL.2.2.2
            by_cases hD1 : K.isD1 i <;>
              simp only [hn, hmL, isNorm, isML, isMbad, hU, hD1, hg, hm, ne_eq, not_true_eq_false, not_false_eq_true,
                and_true, and_false, true_and, false_and, ↓reduceIte] at hprod_rm ⊢ <;>
              (try split_ifs at hprod_rm ⊢) <;> omega
          · have hmb : K.isMbad i := by
              refine ⟨by omega, hU, ?_⟩
              intro hg; by_cases hm : K.M0s.eval (BinaryIRSProfile.domain i ^ 2) = 0
              · exact hn ⟨by omega, hU, hg, hm⟩
              · exact hmL ⟨by omega, hU, hg, hm⟩
            have hM2 : 2 ≤ K.M0s.rootMultiplicity (BinaryIRSProfile.domain i ^ 2) :=
              (le_rootMultiplicity_iff K.hM0s_ne).mpr ((pow_dvd_pow _ (by omega : 2 ≤ D.k i)).trans (K.pow_dvd_M0s_mbad i hU hmb.2.2))
            have hg : ¬ (K.g2t.eval (BinaryIRSProfile.domain i) = 0) := hmb.2.2
            by_cases hD1 : K.isD1 i <;>
              simp only [hn, hmL, hmb, isNorm, isML, isMbad, hU, hD1, hg, ne_eq, not_true_eq_false, not_false_eq_true,
                and_true, and_false, true_and, false_and, ↓reduceIte] at hprod_rm ⊢ <;>
              (try split_ifs at hprod_rm ⊢) <;> omega
      · by_cases hD1 : K.isD1 i <;>
          simp only [isNorm, isML, isMbad, hU, hD1, ne_eq, not_true_eq_false, not_false_eq_true,
            and_true, and_false, true_and, false_and, ↓reduceIte] <;>
          (try split_ifs) <;> omega
    · by_cases hU : S.isU0 i <;> by_cases hD1 : K.isD1 i <;>
        by_cases hg : K.g2t.eval (BinaryIRSProfile.domain i) = 0 <;>
        by_cases hm : K.M0s.eval (BinaryIRSProfile.domain i ^ 2) = 0 <;>
        simp only [isNorm, isML, isMbad, hU, hD1, hg, hm, ne_eq, not_true_eq_false, not_false_eq_true,
          and_true, and_false, true_and, false_and, ↓reduceIte] <;>
        (try split_ifs) <;> omega
  rw [Finset.sum_add_distrib] at hZ
  have h1 : (∑ i : Idx, (K.Lam1.rootMultiplicity (BinaryIRSProfile.domain i ^ 2) : ℤ)) ≤ (K.Lam1.natDegree : ℤ) := by
    exact_mod_cast hsum_lam
  have h2 : (∑ i : Idx, ((if 3 ≤ D.k i ∧ K.isNorm i then K.M0s.rootMultiplicity (BinaryIRSProfile.domain i ^ 2) - 1
      else if 3 ≤ D.k i ∧ K.isMbad i then K.M0s.rootMultiplicity (BinaryIRSProfile.domain i ^ 2) - 2 else 0 : ℕ) : ℤ)) =
      (K.muExK3 : ℤ) := by unfold muExK3; push_cast; rfl
  omega

lemma g1_d2_bound :
    K.d2k0Cnt + K.d2k1UCnt + (2 * D.n2 - S.n2U) + (4 * D.n3 - S.n3U) + 2 * D.nt ≤ (D.gj 1).natDegree := by
  classical
  let f : Idx → ℕ := fun i =>
    if D.k i = 0 then (if K.isD1 i then 1 else 0)
    else if D.k i = 1 then (if S.isU0 i ∧ K.isD1 i then 1 else 0)
    else if S.isU0 i then 2 * D.k i - 3
    else 2 * (D.k i - 1)
  have hdvd : ∀ i ∈ (Finset.univ : Finset Idx), (X - C (BinaryIRSProfile.domain i)) ^ f i ∣ D.gj 1 := fun i _ => by
    dsimp [f]; split_ifs with hk0 hD1 hk1 hD1' hU
    · rw [pow_one]; exact (dvd_iff_isRoot.mpr hD1).trans (S.D1_dvd_gj 1)
    · simp
    · rw [pow_one]; exact (dvd_iff_isRoot.mpr hD1'.2).trans (S.D1_dvd_gj 1)
    · simp
    · exact K.pow_dvd_g1_U0 i
    · exact K.pow_dvd_g1_U1 i hU
  have hle := sum_ord_le_natDegree_of_dvd Finset.univ BinaryIRSProfile.domain BinaryIRSProfile.domain.injective
    (D.gj 1) K.hg1_ne f hdvd
  have hU := S.U_counts_ineqs
  have hZ : ((K.d2k0Cnt : ℤ) + (K.d2k1UCnt : ℤ) + (2 * (D.n2 : ℤ) - (S.n2U : ℤ)) +
      (4 * (D.n3 : ℤ) - (S.n3U : ℤ)) + 2 * (D.nt : ℤ)) = ∑ i : Idx, (f i : ℤ) := by
    have hrew : (K.d2k0Cnt : ℤ) + (K.d2k1UCnt : ℤ) + (2 * (D.n2 : ℤ) - (S.n2U : ℤ)) +
        (4 * (D.n3 : ℤ) - (S.n3U : ℤ)) + 2 * (D.nt : ℤ) =
        ∑ i : Idx, ((if D.k i = 0 ∧ K.isD1 i then (1 : ℤ) else 0) +
          (if D.k i = 1 ∧ S.isU0 i ∧ K.isD1 i then 1 else 0) +
          2 * (if D.k i = 2 then 1 else 0) - (if D.k i = 2 ∧ S.isU0 i then 1 else 0) +
          4 * (if 3 ≤ D.k i then 1 else 0) - (if 3 ≤ D.k i ∧ S.isU0 i then 1 else 0) +
          2 * ((D.k i - 3 : ℕ) : ℤ)) := by
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
        ← n0_Z, ← n1_Z, ← n2_Z, ← n3_Z, ← nt_Z, ← n1U_Z, ← n2U_Z, ← n3U_Z,
        ← K.mbadCnt_Z, ← K.mLCnt_Z, ← K.din2Cnt_Z, ← K.din3Cnt_Z, ← K.dmL2Cnt_Z, ← K.dmL3Cnt_Z,
        ← K.d2k1UCnt_Z, ← K.d2k0Cnt_Z, ← K.mu1Cnt_Z, ← K.ntUNorm_Z, ← K.ntUMbad_Z, ← K.ntUML_Z, ← K.muExK3_Z] <;> ring
    rw [hrew]; apply Finset.sum_congr rfl; intro i _; dsimp [f]
    by_cases hU : S.isU0 i <;> by_cases hD1 : K.isD1 i <;>
      simp only [hU, hD1, and_true, and_false, true_and, false_and, ↓reduceIte] <;>
      (try split_ifs) <;> omega
  rw [← Nat.cast_sum] at hZ; omega

lemma g2_din_bound :
    3 * K.dinCnt + K.d2k1UCnt + K.d2k0Cnt + K.dmLCnt ≤ (D.gj 2).natDegree := by
  classical
  let f : Idx → ℕ := fun i =>
    if K.isNorm i ∧ K.isD1 i then 3
    else if (K.isML i ∧ K.isD1 i) ∨ (D.k i = 1 ∧ S.isU0 i ∧ K.isD1 i) ∨ (D.k i = 0 ∧ K.isD1 i) then 1
    else 0
  have hdvd : ∀ i ∈ (Finset.univ : Finset Idx), (X - C (BinaryIRSProfile.domain i)) ^ f i ∣ D.gj 2 := fun i _ => by
    dsimp [f]; split_ifs with h1 h2
    · exact K.pow_dvd_g2_din i h1.1.1 h1.1.2.1 h1.1.2.2.1 h1.1.2.2.2 h1.2
    · rw [pow_one]
      have hD1 : K.isD1 i := by
        rcases h2 with h | h | h
        · exact h.2
        · exact h.2.2
        · exact h.2
      exact (dvd_iff_isRoot.mpr hD1).trans (S.D1_dvd_gj 2)
    · simp
  have hle := sum_ord_le_natDegree_of_dvd Finset.univ BinaryIRSProfile.domain BinaryIRSProfile.domain.injective
    (D.gj 2) D.g2_ne_zero f hdvd
  have hZ : (3 * (K.dinCnt : ℤ) + (K.d2k1UCnt : ℤ) + (K.d2k0Cnt : ℤ) + (K.dmLCnt : ℤ)) = ∑ i : Idx, (f i : ℤ) := by
    have hrew : 3 * (K.dinCnt : ℤ) + (K.d2k1UCnt : ℤ) + (K.d2k0Cnt : ℤ) + (K.dmLCnt : ℤ) =
        ∑ i : Idx, (3 * (if D.k i = 2 ∧ K.isNorm i ∧ K.isD1 i then (1 : ℤ) else 0) +
          3 * (if 3 ≤ D.k i ∧ K.isNorm i ∧ K.isD1 i then 1 else 0) +
          (if D.k i = 1 ∧ S.isU0 i ∧ K.isD1 i then 1 else 0) +
          (if D.k i = 0 ∧ K.isD1 i then 1 else 0) +
          (if D.k i = 2 ∧ K.isML i ∧ K.isD1 i then 1 else 0) +
          (if 3 ≤ D.k i ∧ K.isML i ∧ K.isD1 i then 1 else 0)) := by
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
        ← n0_Z, ← n1_Z, ← n2_Z, ← n3_Z, ← nt_Z, ← n1U_Z, ← n2U_Z, ← n3U_Z,
        ← K.mbadCnt_Z, ← K.mLCnt_Z, ← K.din2Cnt_Z, ← K.din3Cnt_Z, ← K.dmL2Cnt_Z, ← K.dmL3Cnt_Z,
        ← K.d2k1UCnt_Z, ← K.d2k0Cnt_Z, ← K.mu1Cnt_Z, ← K.ntUNorm_Z, ← K.ntUMbad_Z, ← K.ntUML_Z, ← K.muExK3_Z]
      simp only [dinCnt, dmLCnt, Nat.cast_add]; ring
    rw [hrew]; apply Finset.sum_congr rfl; intro i _; dsimp [f]
    by_cases hU : S.isU0 i <;> by_cases hD1 : K.isD1 i <;>
      by_cases hg : K.g2t.eval (BinaryIRSProfile.domain i) = 0 <;>
      by_cases hm : K.M0s.eval (BinaryIRSProfile.domain i ^ 2) = 0 <;>
      simp only [isNorm, isML, hU, hD1, hg, hm, ne_eq, not_true_eq_false, not_false_eq_true,
        and_true, and_false, true_and, false_and, or_true, or_false, true_or, false_or, ↓reduceIte] <;>
      (try split_ifs) <;> omega
  rw [← Nat.cast_sum] at hZ; omega

lemma g2_din2_full_bound :
    3 * K.din2Cnt + K.dmL2Cnt + K.d2k1UCnt + K.d2k0Cnt + (2 * D.n3 - S.n3U) + 2 * D.nt ≤ (D.gj 2).natDegree := by
  classical
  let f : Idx → ℕ := fun i =>
    if D.k i = 0 then (if K.isD1 i then 1 else 0)
    else if D.k i = 1 then (if S.isU0 i ∧ K.isD1 i then 1 else 0)
    else if D.k i = 2 then (if K.isNorm i ∧ K.isD1 i then 3 else if K.isML i ∧ K.isD1 i then 1 else 0)
    else if S.isU0 i then 2 * D.k i - 5
    else 2 * (D.k i - 2)
  have hdvd : ∀ i ∈ (Finset.univ : Finset Idx), (X - C (BinaryIRSProfile.domain i)) ^ f i ∣ D.gj 2 := fun i _ => by
    dsimp [f]; split_ifs with hk0 hD1 hk1 hD1' hk2 hdin2 hdmL2 hU
    · rw [pow_one]; exact (dvd_iff_isRoot.mpr hD1).trans (S.D1_dvd_gj 2)
    · simp
    · rw [pow_one]; exact (dvd_iff_isRoot.mpr hD1'.2).trans (S.D1_dvd_gj 2)
    · simp
    · exact K.pow_dvd_g2_din i hdin2.1.1 hdin2.1.2.1 hdin2.1.2.2.1 hdin2.1.2.2.2 hdin2.2
    · rw [pow_one]; exact (dvd_iff_isRoot.mpr hdmL2.2).trans (S.D1_dvd_gj 2)
    · simp
    · exact D.pow_dvd_g2_of_k i
    · exact K.pow_dvd_g2_U1 i hU
  have hle := sum_ord_le_natDegree_of_dvd Finset.univ BinaryIRSProfile.domain BinaryIRSProfile.domain.injective
    (D.gj 2) D.g2_ne_zero f hdvd
  have hU := S.U_counts_ineqs
  have hZ : (3 * (K.din2Cnt : ℤ) + (K.dmL2Cnt : ℤ) + (K.d2k1UCnt : ℤ) + (K.d2k0Cnt : ℤ) +
      (2 * (D.n3 : ℤ) - (S.n3U : ℤ)) + 2 * (D.nt : ℤ)) = ∑ i : Idx, (f i : ℤ) := by
    have hrew : 3 * (K.din2Cnt : ℤ) + (K.dmL2Cnt : ℤ) + (K.d2k1UCnt : ℤ) + (K.d2k0Cnt : ℤ) +
        (2 * (D.n3 : ℤ) - (S.n3U : ℤ)) + 2 * (D.nt : ℤ) =
        ∑ i : Idx, (3 * (if D.k i = 2 ∧ K.isNorm i ∧ K.isD1 i then (1 : ℤ) else 0) +
          (if D.k i = 2 ∧ K.isML i ∧ K.isD1 i then 1 else 0) +
          (if D.k i = 1 ∧ S.isU0 i ∧ K.isD1 i then 1 else 0) +
          (if D.k i = 0 ∧ K.isD1 i then 1 else 0) +
          2 * (if 3 ≤ D.k i then 1 else 0) - (if 3 ≤ D.k i ∧ S.isU0 i then 1 else 0) +
          2 * ((D.k i - 3 : ℕ) : ℤ)) := by
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
        ← n0_Z, ← n1_Z, ← n2_Z, ← n3_Z, ← nt_Z, ← n1U_Z, ← n2U_Z, ← n3U_Z,
        ← K.mbadCnt_Z, ← K.mLCnt_Z, ← K.din2Cnt_Z, ← K.din3Cnt_Z, ← K.dmL2Cnt_Z, ← K.dmL3Cnt_Z,
        ← K.d2k1UCnt_Z, ← K.d2k0Cnt_Z, ← K.mu1Cnt_Z, ← K.ntUNorm_Z, ← K.ntUMbad_Z, ← K.ntUML_Z, ← K.muExK3_Z] <;> ring
    rw [hrew]; apply Finset.sum_congr rfl; intro i _; dsimp [f]
    by_cases hU : S.isU0 i <;> by_cases hD1 : K.isD1 i <;>
      by_cases hg : K.g2t.eval (BinaryIRSProfile.domain i) = 0 <;>
      by_cases hm : K.M0s.eval (BinaryIRSProfile.domain i ^ 2) = 0 <;>
      simp only [isNorm, isML, hU, hD1, hg, hm, ne_eq, not_true_eq_false, not_false_eq_true,
        and_true, and_false, true_and, false_and, ↓reduceIte] <;>
      (try split_ifs) <;> omega
  rw [← Nat.cast_sum] at hZ; omega

lemma ResY_uncond_bound :
    4 * K.d2k0Cnt + 3 * K.d2k1UCnt + 12 * K.din2Cnt + 2 * K.dmL2Cnt +
      (4 * D.n1 - 3 * S.n1U) + (16 * D.n2 - 5 * S.n2U) + (34 * D.n3 - 5 * S.n3U) + 18 * D.nt ≤
      D.ResY.natDegree := by
  classical
  let f : Idx → ℕ := fun i =>
    if D.k i = 0 ∧ K.isD1 i then 4
    else if D.k i = 1 ∧ S.isU0 i ∧ K.isD1 i then 4
    else if D.k i = 2 ∧ K.isNorm i ∧ K.isD1 i then 23
    else if D.k i = 2 ∧ K.isML i ∧ K.isD1 i then 13
    else if S.isU0 i then KerD45Data.resOrdU0 (D.k i) else KerD45Data.resOrdU1 (D.k i)
  have hdvd : ∀ i ∈ (Finset.univ : Finset Idx), (X - C (BinaryIRSProfile.domain i)) ^ f i ∣ D.ResY := fun i _ => by
    dsimp [f]; split_ifs with h0 h1 h2n h2m hU
    · rw [K.hResY_fac]; exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (pow_dvd_pow_of_dvd (dvd_iff_isRoot.mpr h0.2) 4) _) _) _
    · rw [K.hResY_fac]; exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (pow_dvd_pow_of_dvd (dvd_iff_isRoot.mpr h1.2.2) 4) _) _) _
    · rw [K.hResY_fac]
      have hdD : (X - C (BinaryIRSProfile.domain i)) ^ 4 ∣ S.D1 ^ 4 := pow_dvd_pow_of_dvd (dvd_iff_isRoot.mpr h2n.2.2) 4
      have hdL : (X - C (BinaryIRSProfile.domain i)) ^ 8 ∣ K.Lam1.comp (X ^ 2) ^ 4 := by
        have hL1 := K.pow_dvd_Lam1_d2 i h2n.2.2; rw [h2n.1] at hL1
        have hL2 := (pow_dvd_comp_X_sq_iff K.Lam1 (BinaryIRSProfile.domain i) 1).mpr hL1
        rw [show (8 : ℕ) = 2 * 4 by rfl, pow_mul]; exact pow_dvd_pow_of_dvd hL2 4
      have hdM : (X - C (BinaryIRSProfile.domain i)) ^ 10 ∣ K.M0s.comp (X ^ 2) ^ 5 := by
        have hM2 := (pow_dvd_comp_X_sq_iff K.M0s (BinaryIRSProfile.domain i) 1).mpr (by rw [pow_one]; exact dvd_iff_isRoot.mpr h2n.2.1.2.2.2)
        rw [show (10 : ℕ) = 2 * 5 by rfl, pow_mul]; exact pow_dvd_pow_of_dvd hM2 5
      have hdg : (X - C (BinaryIRSProfile.domain i)) ^ 1 ∣ K.g2t := by rw [pow_one]; exact dvd_iff_isRoot.mpr h2n.2.1.2.2.1
      rw [show (23 : ℕ) = 4 + 8 + 10 + 1 by rfl, pow_add, pow_add, pow_add]
      exact mul_dvd_mul (mul_dvd_mul (mul_dvd_mul hdD hdL) hdM) hdg
    · rw [K.hResY_fac]
      have hdD : (X - C (BinaryIRSProfile.domain i)) ^ 4 ∣ S.D1 ^ 4 := pow_dvd_pow_of_dvd (dvd_iff_isRoot.mpr h2m.2.2) 4
      have hdL : (X - C (BinaryIRSProfile.domain i)) ^ 8 ∣ K.Lam1.comp (X ^ 2) ^ 4 := by
        have hL1 := K.pow_dvd_Lam1_d2 i h2m.2.2; rw [h2m.1] at hL1
        have hL2 := (pow_dvd_comp_X_sq_iff K.Lam1 (BinaryIRSProfile.domain i) 1).mpr hL1
        rw [show (8 : ℕ) = 2 * 4 by rfl, pow_mul]; exact pow_dvd_pow_of_dvd hL2 4
      have hdg : (X - C (BinaryIRSProfile.domain i)) ^ 1 ∣ K.g2t := by rw [pow_one]; exact dvd_iff_isRoot.mpr h2m.2.1.2.2.1
      rw [show (13 : ℕ) = 4 + 8 + 0 + 1 by rfl, pow_add, pow_add, pow_add, pow_zero]
      exact mul_dvd_mul (mul_dvd_mul (mul_dvd_mul hdD hdL) (one_dvd _)) hdg
    · exact D.pow_dvd_ResY_U0 i
    · exact S.pow_dvd_ResY_U1 i hU
  have hle := sum_ord_le_natDegree_of_dvd Finset.univ BinaryIRSProfile.domain BinaryIRSProfile.domain.injective
    D.ResY D.ResY_ne_zero f hdvd
  have hU := S.U_counts_ineqs
  have hZ : (4 * (K.d2k0Cnt : ℤ) + 3 * (K.d2k1UCnt : ℤ) + 12 * (K.din2Cnt : ℤ) + 2 * (K.dmL2Cnt : ℤ) +
      (4 * (D.n1 : ℤ) - 3 * (S.n1U : ℤ)) + (16 * (D.n2 : ℤ) - 5 * (S.n2U : ℤ)) +
      (34 * (D.n3 : ℤ) - 5 * (S.n3U : ℤ)) + 18 * (D.nt : ℤ)) = ∑ i : Idx, (f i : ℤ) := by
    have hrew : 4 * (K.d2k0Cnt : ℤ) + 3 * (K.d2k1UCnt : ℤ) + 12 * (K.din2Cnt : ℤ) + 2 * (K.dmL2Cnt : ℤ) +
        (4 * (D.n1 : ℤ) - 3 * (S.n1U : ℤ)) + (16 * (D.n2 : ℤ) - 5 * (S.n2U : ℤ)) +
        (34 * (D.n3 : ℤ) - 5 * (S.n3U : ℤ)) + 18 * (D.nt : ℤ) =
        ∑ i : Idx, (4 * (if D.k i = 0 ∧ K.isD1 i then (1 : ℤ) else 0) +
          3 * (if D.k i = 1 ∧ S.isU0 i ∧ K.isD1 i then 1 else 0) +
          12 * (if D.k i = 2 ∧ K.isNorm i ∧ K.isD1 i then 1 else 0) +
          2 * (if D.k i = 2 ∧ K.isML i ∧ K.isD1 i then 1 else 0) +
          4 * (if D.k i = 1 then 1 else 0) - 3 * (if D.k i = 1 ∧ S.isU0 i then 1 else 0) +
          16 * (if D.k i = 2 then 1 else 0) - 5 * (if D.k i = 2 ∧ S.isU0 i then 1 else 0) +
          34 * (if 3 ≤ D.k i then 1 else 0) - 5 * (if 3 ≤ D.k i ∧ S.isU0 i then 1 else 0) +
          18 * ((D.k i - 3 : ℕ) : ℤ)) := by
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
        ← n0_Z, ← n1_Z, ← n2_Z, ← n3_Z, ← nt_Z, ← n1U_Z, ← n2U_Z, ← n3U_Z,
        ← K.mbadCnt_Z, ← K.mLCnt_Z, ← K.din2Cnt_Z, ← K.din3Cnt_Z, ← K.dmL2Cnt_Z, ← K.dmL3Cnt_Z,
        ← K.d2k1UCnt_Z, ← K.d2k0Cnt_Z, ← K.mu1Cnt_Z, ← K.ntUNorm_Z, ← K.ntUMbad_Z, ← K.ntUML_Z, ← K.muExK3_Z] <;> ring
    rw [hrew]; apply Finset.sum_congr rfl; intro i _
    dsimp [f]
    by_cases hU : S.isU0 i <;> by_cases hD1 : K.isD1 i <;>
      by_cases hg : K.g2t.eval (BinaryIRSProfile.domain i) = 0 <;>
      by_cases hm : K.M0s.eval (BinaryIRSProfile.domain i ^ 2) = 0 <;>
      simp only [isNorm, isML, KerD45Data.resOrdU0, KerD45Data.resOrdU1, hU, hD1, hg, hm,
        ne_eq, not_true_eq_false, not_false_eq_true, and_true, and_false, true_and, false_and, ↓reduceIte] <;>
      (try split_ifs) <;> omega
  rw [← Nat.cast_sum] at hZ; omega

lemma ResY_eK_bound :
    4 * (K.d2k0Cnt : ℤ) + 3 * (K.d2k1UCnt : ℤ) + 20 * (K.din2Cnt : ℤ) + 10 * (K.dmL2Cnt : ℤ) -
      8 * ((K.K1.natDegree - ((D.n2 - S.n2U) + (2 * D.n3 - S.n3U) + D.nt) : ℕ) : ℤ) +
      (4 * (D.n1 : ℤ) - 3 * (S.n1U : ℤ)) + (16 * (D.n2 : ℤ) - 5 * (S.n2U : ℤ)) +
      (34 * (D.n3 : ℤ) - 5 * (S.n3U : ℤ)) + 18 * (D.nt : ℤ) ≤ (D.ResY.natDegree : ℤ) := by
  classical
  have hsum_Res : ∑ i : Idx, D.ResY.rootMultiplicity (BinaryIRSProfile.domain i) ≤ D.ResY.natDegree :=
    sum_ord_le_natDegree_of_dvd Finset.univ BinaryIRSProfile.domain BinaryIRSProfile.domain.injective
      D.ResY D.ResY_ne_zero _ (fun i _ => pow_rootMultiplicity_dvd D.ResY _)
  have hsum_K1 : ∑ i : Idx, K.K1.rootMultiplicity (BinaryIRSProfile.domain i ^ 2) ≤ K.K1.natDegree :=
    sum_ord_le_natDegree_of_dvd Finset.univ (fun i => BinaryIRSProfile.domain i ^ 2)
      domain_sq_injective K.K1 K.hK1_ne _ (fun i _ => pow_rootMultiplicity_dvd K.K1 _)
  let baseK1 : Idx → ℕ := fun i =>
    if D.k i ≤ 1 then 0 else if S.isU0 i then D.k i - 2 else D.k i - 1
  have hbaseK1_le : ∀ i : Idx, baseK1 i ≤ K.K1.rootMultiplicity (BinaryIRSProfile.domain i ^ 2) := fun i => by
    apply (le_rootMultiplicity_iff K.hK1_ne).mpr
    dsimp [baseK1]; split_ifs with hk hU
    · simp
    · exact K.pow_dvd_K1_all i
    · exact K.pow_dvd_K1_U1 i hU
  have hU := S.U_counts_ineqs
  have hbaseK1_sum : (∑ i : Idx, (baseK1 i : ℤ)) = ((D.n2 : ℤ) - (S.n2U : ℤ)) + (2 * (D.n3 : ℤ) - (S.n3U : ℤ)) + (D.nt : ℤ) := by
    have hrew : ((D.n2 : ℤ) - (S.n2U : ℤ)) + (2 * (D.n3 : ℤ) - (S.n3U : ℤ)) + (D.nt : ℤ) =
        ∑ i : Idx, ((if D.k i = 2 then (1 : ℤ) else 0) - (if D.k i = 2 ∧ S.isU0 i then 1 else 0) +
          2 * (if 3 ≤ D.k i then 1 else 0) - (if 3 ≤ D.k i ∧ S.isU0 i then 1 else 0) + ((D.k i - 3 : ℕ) : ℤ)) := by
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
        ← n0_Z, ← n1_Z, ← n2_Z, ← n3_Z, ← nt_Z, ← n1U_Z, ← n2U_Z, ← n3U_Z,
        ← K.mbadCnt_Z, ← K.mLCnt_Z, ← K.din2Cnt_Z, ← K.din3Cnt_Z, ← K.dmL2Cnt_Z, ← K.dmL3Cnt_Z,
        ← K.d2k1UCnt_Z, ← K.d2k0Cnt_Z, ← K.mu1Cnt_Z, ← K.ntUNorm_Z, ← K.ntUMbad_Z, ← K.ntUML_Z, ← K.muExK3_Z] <;> ring
    rw [hrew]; apply Finset.sum_congr rfl; intro i _; dsimp [baseK1]
    by_cases hU : S.isU0 i <;>
      simp only [hU, and_true, and_false, true_and, false_and, ↓reduceIte] <;>
      (try split_ifs) <;> omega
  have heK_ge : ∑ i : Idx, ((K.K1.rootMultiplicity (BinaryIRSProfile.domain i ^ 2) : ℤ) - (baseK1 i : ℤ)) ≤
      ((K.K1.natDegree - ((D.n2 - S.n2U) + (2 * D.n3 - S.n3U) + D.nt) : ℕ) : ℤ) := by
    rw [Finset.sum_sub_distrib, hbaseK1_sum]
    have hK1b' : (D.n2 - S.n2U) + (2 * D.n3 - S.n3U) + D.nt ≤ K.K1.natDegree :=
      Nat.le_trans (Nat.le_add_right _ _) K.K1_base_le
    have h1 : (∑ i : Idx, (K.K1.rootMultiplicity (BinaryIRSProfile.domain i ^ 2) : ℤ)) ≤ (K.K1.natDegree : ℤ) := by
      exact_mod_cast hsum_K1
    have h2 : S.n2U ≤ D.n2 := hU.2.1
    have h3 : S.n3U ≤ 2 * D.n3 := by have := hU.2.2.1; omega
    simp only [Nat.cast_sub hK1b', Nat.cast_add, Nat.cast_sub h2, Nat.cast_sub h3, Nat.cast_mul, Nat.cast_ofNat]
    linarith only [h1]
  have hpt : ∀ i : Idx,
      4 * (if D.k i = 0 ∧ K.isD1 i then (1 : ℤ) else 0) +
      3 * (if D.k i = 1 ∧ S.isU0 i ∧ K.isD1 i then 1 else 0) +
      20 * (if D.k i = 2 ∧ K.isNorm i ∧ K.isD1 i then 1 else 0) +
      10 * (if D.k i = 2 ∧ K.isML i ∧ K.isD1 i then 1 else 0) +
      4 * (if D.k i = 1 then 1 else 0) - 3 * (if D.k i = 1 ∧ S.isU0 i then 1 else 0) +
      16 * (if D.k i = 2 then 1 else 0) - 5 * (if D.k i = 2 ∧ S.isU0 i then 1 else 0) +
      34 * (if 3 ≤ D.k i then 1 else 0) - 5 * (if 3 ≤ D.k i ∧ S.isU0 i then 1 else 0) +
      18 * ((D.k i - 3 : ℕ) : ℤ) ≤
      (D.ResY.rootMultiplicity (BinaryIRSProfile.domain i) : ℤ) +
        8 * ((K.K1.rootMultiplicity (BinaryIRSProfile.domain i ^ 2) : ℤ) - (baseK1 i : ℤ)) := by
    intro i
    have hk1_nn : (0 : ℤ) ≤ (K.K1.rootMultiplicity (BinaryIRSProfile.domain i ^ 2) : ℤ) - (baseK1 i : ℤ) := by
      have := hbaseK1_le i; omega
    by_cases h2n : D.k i = 2 ∧ K.isNorm i ∧ K.isD1 i
    · have hKL : 2 ≤ K.K1.rootMultiplicity (BinaryIRSProfile.domain i ^ 2) + K.Lam1.rootMultiplicity (BinaryIRSProfile.domain i ^ 2) := by
        have hd := K.pow_dvd_K_M10sh_d2 i h2n.2.2
        simp only [h2n.1, show ¬ (2 ≤ 1) by omega, ↓reduceIte] at hd
        have hle := (le_rootMultiplicity_iff (mul_ne_zero K.hK1_ne K.hLam1_ne)).mpr hd
        rwa [rootMultiplicity_mul (mul_ne_zero K.hK1_ne K.hLam1_ne)] at hle
      have hRes_rm : D.ResY.rootMultiplicity (BinaryIRSProfile.domain i) =
          4 * S.D1.rootMultiplicity (BinaryIRSProfile.domain i) +
          8 * K.Lam1.rootMultiplicity (BinaryIRSProfile.domain i ^ 2) +
          10 * K.M0s.rootMultiplicity (BinaryIRSProfile.domain i ^ 2) +
          K.g2t.rootMultiplicity (BinaryIRSProfile.domain i) := by
        have hL_ne := mt (comp_X_sq_eq_zero_iff K.Lam1).mp K.hLam1_ne
        have hM_ne := mt (comp_X_sq_eq_zero_iff K.M0s).mp K.hM0s_ne
        rw [K.hResY_fac,
          rootMultiplicity_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero 4 S.D1_ne_zero) (pow_ne_zero 4 hL_ne)) (pow_ne_zero 5 hM_ne)) K.hg2t_ne),
          rootMultiplicity_mul (mul_ne_zero (mul_ne_zero (pow_ne_zero 4 S.D1_ne_zero) (pow_ne_zero 4 hL_ne)) (pow_ne_zero 5 hM_ne)),
          rootMultiplicity_mul (mul_ne_zero (pow_ne_zero 4 S.D1_ne_zero) (pow_ne_zero 4 hL_ne)),
          rootMultiplicity_pow_eq' S.D1 S.D1_ne_zero 4 _,
          rootMultiplicity_pow_eq' _ hL_ne 4 _,
          rootMultiplicity_pow_eq' _ hM_ne 5 _,
          show (K.Lam1.comp (X ^ 2)).rootMultiplicity (BinaryIRSProfile.domain i) = 2 * K.Lam1.rootMultiplicity (BinaryIRSProfile.domain i ^ 2) by
            rw [← rootMultiplicity_map_eq, rootMultiplicity_comp_X_sq_map K.Lam1 K.hLam1_ne, ← map_pow, rootMultiplicity_map_eq],
          show (K.M0s.comp (X ^ 2)).rootMultiplicity (BinaryIRSProfile.domain i) = 2 * K.M0s.rootMultiplicity (BinaryIRSProfile.domain i ^ 2) by
            rw [← rootMultiplicity_map_eq, rootMultiplicity_comp_X_sq_map K.M0s K.hM0s_ne, ← map_pow, rootMultiplicity_map_eq]]
        ring
      have hD1_1 : 1 ≤ S.D1.rootMultiplicity (BinaryIRSProfile.domain i) :=
        (le_rootMultiplicity_iff S.D1_ne_zero).mpr (by rw [pow_one]; exact dvd_iff_isRoot.mpr h2n.2.2)
      have hM_1 : 1 ≤ K.M0s.rootMultiplicity (BinaryIRSProfile.domain i ^ 2) :=
        (le_rootMultiplicity_iff K.hM0s_ne).mpr (by rw [pow_one]; exact dvd_iff_isRoot.mpr h2n.2.1.2.2.2)
      have hg_1 : 1 ≤ K.g2t.rootMultiplicity (BinaryIRSProfile.domain i) :=
        (le_rootMultiplicity_iff K.hg2t_ne).mpr (by rw [pow_one]; exact dvd_iff_isRoot.mpr h2n.2.1.2.2.1)
      have hb0 : baseK1 i = 0 := by dsimp [baseK1]; rw [if_neg (by omega), if_pos h2n.2.1.2.1]; omega
      have hnML : ¬ K.isML i := fun h => h.2.2.2 h2n.2.1.2.2.2
      simp only [h2n.1, h2n.2.1, h2n.2.2, h2n.2.1.2.1, hnML, show (2 : ℕ) ≠ 0 by omega, show (2 : ℕ) ≠ 1 by omega,
        show ¬ (3 ≤ 2) by omega, Nat.sub_eq_zero_of_le (show 2 ≤ 3 by omega), hb0, ↓reduceIte, and_true, false_and, true_and]
      omega
    · by_cases h2m : D.k i = 2 ∧ K.isML i ∧ K.isD1 i
      · have hKL : 2 ≤ K.K1.rootMultiplicity (BinaryIRSProfile.domain i ^ 2) + K.Lam1.rootMultiplicity (BinaryIRSProfile.domain i ^ 2) := by
          have hd := K.pow_dvd_K_M10sh_d2 i h2m.2.2
          simp only [h2m.1, show ¬ (2 ≤ 1) by omega, ↓reduceIte] at hd
          have hle := (le_rootMultiplicity_iff (mul_ne_zero K.hK1_ne K.hLam1_ne)).mpr hd
          rwa [rootMultiplicity_mul (mul_ne_zero K.hK1_ne K.hLam1_ne)] at hle
        have hRes_rm : D.ResY.rootMultiplicity (BinaryIRSProfile.domain i) =
            4 * S.D1.rootMultiplicity (BinaryIRSProfile.domain i) +
            8 * K.Lam1.rootMultiplicity (BinaryIRSProfile.domain i ^ 2) +
            10 * K.M0s.rootMultiplicity (BinaryIRSProfile.domain i ^ 2) +
            K.g2t.rootMultiplicity (BinaryIRSProfile.domain i) := by
          have hL_ne := mt (comp_X_sq_eq_zero_iff K.Lam1).mp K.hLam1_ne
          have hM_ne := mt (comp_X_sq_eq_zero_iff K.M0s).mp K.hM0s_ne
          rw [K.hResY_fac,
            rootMultiplicity_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero 4 S.D1_ne_zero) (pow_ne_zero 4 hL_ne)) (pow_ne_zero 5 hM_ne)) K.hg2t_ne),
            rootMultiplicity_mul (mul_ne_zero (mul_ne_zero (pow_ne_zero 4 S.D1_ne_zero) (pow_ne_zero 4 hL_ne)) (pow_ne_zero 5 hM_ne)),
            rootMultiplicity_mul (mul_ne_zero (pow_ne_zero 4 S.D1_ne_zero) (pow_ne_zero 4 hL_ne)),
            rootMultiplicity_pow_eq' S.D1 S.D1_ne_zero 4 _,
            rootMultiplicity_pow_eq' _ hL_ne 4 _,
            rootMultiplicity_pow_eq' _ hM_ne 5 _,
            show (K.Lam1.comp (X ^ 2)).rootMultiplicity (BinaryIRSProfile.domain i) = 2 * K.Lam1.rootMultiplicity (BinaryIRSProfile.domain i ^ 2) by
              rw [← rootMultiplicity_map_eq, rootMultiplicity_comp_X_sq_map K.Lam1 K.hLam1_ne, ← map_pow, rootMultiplicity_map_eq],
            show (K.M0s.comp (X ^ 2)).rootMultiplicity (BinaryIRSProfile.domain i) = 2 * K.M0s.rootMultiplicity (BinaryIRSProfile.domain i ^ 2) by
              rw [← rootMultiplicity_map_eq, rootMultiplicity_comp_X_sq_map K.M0s K.hM0s_ne, ← map_pow, rootMultiplicity_map_eq]]
          ring
        have hD1_1 : 1 ≤ S.D1.rootMultiplicity (BinaryIRSProfile.domain i) :=
          (le_rootMultiplicity_iff S.D1_ne_zero).mpr (by rw [pow_one]; exact dvd_iff_isRoot.mpr h2m.2.2)
        have hg_1 : 1 ≤ K.g2t.rootMultiplicity (BinaryIRSProfile.domain i) :=
          (le_rootMultiplicity_iff K.hg2t_ne).mpr (by rw [pow_one]; exact dvd_iff_isRoot.mpr h2m.2.1.2.2.1)
        have hb0 : baseK1 i = 0 := by dsimp [baseK1]; rw [if_neg (by omega), if_pos h2m.2.1.2.1]; omega
        have hnN : ¬ K.isNorm i := fun h => h2m.2.1.2.2.2 h.2.2.2
        simp only [h2m.1, h2m.2.1, h2m.2.2, h2m.2.1.2.1, hnN, show (2 : ℕ) ≠ 0 by omega, show (2 : ℕ) ≠ 1 by omega,
          show ¬ (3 ≤ 2) by omega, Nat.sub_eq_zero_of_le (show 2 ≤ 3 by omega), hb0, ↓reduceIte, and_true, false_and, true_and]
        omega
      · have hRes_base : (if D.k i = 0 ∧ K.isD1 i then 4
            else if D.k i = 1 ∧ S.isU0 i ∧ K.isD1 i then 4
            else if S.isU0 i then KerD45Data.resOrdU0 (D.k i) else KerD45Data.resOrdU1 (D.k i)) ≤
            D.ResY.rootMultiplicity (BinaryIRSProfile.domain i) := by
          apply (le_rootMultiplicity_iff D.ResY_ne_zero).mpr
          split_ifs with h0 h1 hU
          · rw [K.hResY_fac]; exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (pow_dvd_pow_of_dvd (dvd_iff_isRoot.mpr h0.2) 4) _) _) _
          · rw [K.hResY_fac]; exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (pow_dvd_pow_of_dvd (dvd_iff_isRoot.mpr h1.2.2) 4) _) _) _
          · exact D.pow_dvd_ResY_U0 i
          · exact S.pow_dvd_ResY_U1 i hU
        unfold KerD45Data.resOrdU0 KerD45Data.resOrdU1 at hRes_base
        by_cases hU : S.isU0 i <;> by_cases hD1 : K.isD1 i <;>
          by_cases hg : K.g2t.eval (BinaryIRSProfile.domain i) = 0 <;>
          by_cases hm : K.M0s.eval (BinaryIRSProfile.domain i ^ 2) = 0 <;>
          simp only [isNorm, isML, hU, hD1, hg, hm, ne_eq, not_true_eq_false, not_false_eq_true,
            and_true, and_false, true_and, false_and, ↓reduceIte] at h2n h2m hRes_base ⊢ <;>
          (try split_ifs at hRes_base ⊢) <;> omega
  have htot := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hpt i)
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
        ← n0_Z, ← n1_Z, ← n2_Z, ← n3_Z, ← nt_Z, ← n1U_Z, ← n2U_Z, ← n3U_Z,
        ← K.mbadCnt_Z, ← K.mLCnt_Z, ← K.din2Cnt_Z, ← K.din3Cnt_Z, ← K.dmL2Cnt_Z, ← K.dmL3Cnt_Z,
        ← K.d2k1UCnt_Z, ← K.d2k0Cnt_Z, ← K.mu1Cnt_Z, ← K.ntUNorm_Z, ← K.ntUMbad_Z, ← K.ntUML_Z, ← K.muExK3_Z] at htot
  rw [Finset.sum_sub_distrib] at heK_ge
  have hR_Z : (∑ i : Idx, (D.ResY.rootMultiplicity (BinaryIRSProfile.domain i) : ℤ)) ≤ (D.ResY.natDegree : ℤ) := by
    exact_mod_cast hsum_Res
  linarith [heK_ge, hR_Z]

end KerD45KData
end B6402Table4K
end ProximityPrize.SubmissionBinaryLower
