import ProximityPrize.SubmissionBinaryLower.Binary6402Table4CommonPart4
import ProximityPrize.SubmissionBinaryLower.B6401Params
import ProximityPrize.SubmissionBinaryLower.B6401ContactKerD
import ProximityPrize.SubmissionBinaryLower.B6401QuotInterp
import ProximityPrize.SubmissionBinaryLower.B6401ResultantOrd
import ProximityPrize.SubmissionBinaryLower.B6401KerDOrders
import ProximityPrize.SubmissionBinaryLower.Binary6402IntFarkas
import ProximityPrize.SubmissionBinaryLower.Binary6402T4Rows
import ProximityPrize.SubmissionBinaryLower.P64Resultant
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.Tactic

set_option Elab.async false
set_option maxHeartbeats 600000
set_option maxRecDepth 1024

/-!
# Table 4 Common `ker(D)` `(d₁ = 4, d₀ ≤ 5)` Algebra, Resultant Bounds, `det`, and `p0_zero`

Provides the shared algebraic foundation for all 120 Table 4 branches (`B6401Table4NonK` and
`B6401Table4K`), plus complete proofs for `T4ABranch.det` and `T4ABranch.p0Zero`:
1. `SparseRow` / `baseT4Rows` satisfaction bridge matching `B6402IntFarkas.checkT4Bucket_sound`
   and `B6402T4Rows.buildT4ARows` / `buildT4BRows` definitionally.
2. Exact char-2 polynomial helpers (`sqrtPoly`, `evenPart`, `oddPart`, `sum_ord_le_natDegree`).
3. Extraction of `P_j, C_j, B_j, g_j` (`j : Fin 3`) from `f_coord : KerDIdx wY W_F 1 → Fld`
   (`W_F < 6 * wY - 1`), exact degree bounds, and shifted `(A0_j, A1_j, B^{sh}_j)` local orders.
4. Universal formal `(5, 4)` Sylvester resultant theorems:
   - `f1_eval_P_ne_zero`,
   - `natDegree_resultant_5_4_le_sylvester` (`deg_X(Res_Y) ≤ 8 W_F - 20 wY + 4 + deg_X(g_4)`),
   - `pow_dvd_resultant_5_4_U0` (`1, 11, 29 + 18(k - 3)`) and `_U1` (`4, 16, 34 + 18(k - 3)`).
5. `T4ABranch.det` (`det M ≠ 0`) and `T4ABranch.p0Zero` (`det M = 0, p = 0`) satisfaction proofs.
6. `KerD45Syzygy` (`det M = 0, p ≠ 0, U(X, P) ≠ 0`): exact coprime `(p, c, b)`, reduced minors
   `M21, M20, M10`, `Res_Y = H1 * Q2(X^2)^2`, squarefree `D2 = gcd(p, q)` & `D1 = sqrtPoly D2`,
   `D1 ∣ g_j, R, U_P`, `D1^5 ∣ H1`, all shifted local order bounds, and all degree bounds.
-/

namespace ProximityPrize.SubmissionBinaryLower
namespace B6402Table4Common

open Polynomial B6401ContactKerD B6401QuotInterp B6401ResultantOrd
open B6401Params hiding A D
open B6402HybridP64 (A)
open B6401KerDOrders B6402IntFarkas B6402T4Rows
open ProximityPrize.Benchmark ProximityPrize.Benchmark.Binary
open scoped BigOperators
local notation (priority := high) "X" => Polynomial.X

local notation "Fld" => BinaryIRSProfile.Field
local notation "Idx" => BinaryIRSProfile.Index
namespace KerD45Data
variable (D : KerD45Data)

lemma n_sum_eq_N : D.n0 + D.n1 + D.n2 + D.n3 = N := by
  have hgen : ∀ S : Finset Idx,
      (S.filter fun i => D.k i = 0).card + (S.filter fun i => D.k i = 1).card +
      (S.filter fun i => D.k i = 2).card + (S.filter fun i => 3 ≤ D.k i).card = S.card := by
    intro S
    have h1 : ∑ _i ∈ S, (1 : ℕ) =
        (∑ i ∈ S, if D.k i = 0 then 1 else 0) + (∑ i ∈ S, if D.k i = 1 then 1 else 0) +
        (∑ i ∈ S, if D.k i = 2 then 1 else 0) + (∑ i ∈ S, if 3 ≤ D.k i then 1 else 0) := by
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro i _; split_ifs <;> omega
    simp only [Finset.sum_const, smul_eq_mul, mul_one, ← Finset.card_filter] at h1
    exact h1.symm
  unfold n0 n1 n2 n3
  exact (hgen Finset.univ).trans BinaryIRSProfile.card_index

lemma a_sum_eq_card : D.a0 + D.a1 + D.a2 + D.a3 = D.Az.card := by
  have h1 : ∑ i ∈ D.Az, (1 : ℕ) =
      (∑ i ∈ D.Az, if D.k i = 0 then 1 else 0) + (∑ i ∈ D.Az, if D.k i = 1 then 1 else 0) +
      (∑ i ∈ D.Az, if D.k i = 2 then 1 else 0) + (∑ i ∈ D.Az, if 3 ≤ D.k i then 1 else 0) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro i _; split_ifs <;> omega
  simp only [Finset.sum_const, smul_eq_mul, mul_one, ← Finset.card_filter] at h1
  unfold a0 a1 a2 a3; exact h1.symm

lemma a_le_n : D.a0 ≤ D.n0 ∧ D.a1 ≤ D.n1 ∧ D.a2 ≤ D.n2 ∧ D.a3 ≤ D.n3 := by
  unfold a0 a1 a2 a3 n0 n1 n2 n3
  refine ⟨Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_univ _)),
          Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_univ _)),
          Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_univ _)),
          Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_univ _))⟩

lemma a1_3a2_5a3_le : D.a1 + 3 * D.a2 + 5 * D.a3 ≤ D.W_F - wY + 1 := by
  have hsum : D.a1 + 3 * D.a2 + 5 * D.a3 ≤ ∑ i ∈ D.Az, (2 * D.k i - 1) := by
    have hrew : D.a1 + 3 * D.a2 + 5 * D.a3 =
        ∑ i ∈ D.Az, ((if D.k i = 1 then 1 else 0) + (if D.k i = 2 then 3 else 0) + (if 3 ≤ D.k i then 5 else 0)) := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
      simp only [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, smul_eq_mul, mul_one]
      unfold a1 a2 a3; ring
    rw [hrew]; apply Finset.sum_le_sum; intro i _; split_ifs <;> omega
  exact hsum.trans ((sum_ord_le_natDegree_of_dvd D.Az BinaryIRSProfile.domain BinaryIRSProfile.domain.injective
    (D.f1.eval D.P) D.f1_eval_P_ne_zero _ D.pow_dvd_f1_eval_P).trans D.natDegree_f1_eval_P_le)

lemma n3_2nt_le : D.n3 + 2 * D.nt ≤ D.W_F + 1 - 5 * wY := by
  have hsum : D.n3 + 2 * D.nt = ∑ i : Idx, (2 * D.k i - 5) := by
    have hgen : ∀ S : Finset Idx,
        (S.filter fun i => 3 ≤ D.k i).card + 2 * ∑ i ∈ S, (D.k i - 3) = ∑ i ∈ S, (2 * D.k i - 5) := by
      intro S
      have hrew : (S.filter fun i => 3 ≤ D.k i).card + 2 * ∑ i ∈ S, (D.k i - 3) =
          ∑ i ∈ S, ((if 3 ≤ D.k i then 1 else 0) + 2 * (D.k i - 3)) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum]
        simp only [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, smul_eq_mul, mul_one]
      rw [hrew]; apply Finset.sum_congr rfl; intro i _; split_ifs <;> omega
    unfold n3 nt; exact hgen Finset.univ
  rw [hsum]
  exact (sum_ord_le_natDegree_of_dvd Finset.univ BinaryIRSProfile.domain BinaryIRSProfile.domain.injective
    (D.gj 2) D.g2_ne_zero _ (fun i _ => D.pow_dvd_g2_of_k i)).trans (D.natDegree_gj_le 2)

end KerD45Data
end B6402Table4Common
end ProximityPrize.SubmissionBinaryLower
