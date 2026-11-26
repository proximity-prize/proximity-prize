import ProximityPrize.SubmissionBinaryLower.Binary6402Table4CommonPart16
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
namespace KerD45Syzygy
variable {D : KerD45Data} (S : KerD45Syzygy D)

lemma f1_eval_P_U_bound :
    (2 * D.a1 - S.a1U) + (4 * D.a2 - S.a2U) + (6 * D.a3 - S.a3U) ≤ D.W_F - wY + 1 := by
  classical
  have hdvd : ∀ i ∈ D.Az,
      (X - C (BinaryIRSProfile.domain i)) ^ (if S.isU0 i then 2 * D.k i - 1 else 2 * D.k i) ∣ D.f1.eval D.P :=
    fun i hi => by
      split_ifs with hU
      · exact D.pow_dvd_f1_eval_P i hi
      · exact S.pow_dvd_f1_eval_P_U1 i hi hU
  have hle := (sum_ord_le_natDegree_of_dvd D.Az BinaryIRSProfile.domain BinaryIRSProfile.domain.injective
    (D.f1.eval D.P) D.f1_eval_P_ne_zero _ hdvd).trans D.natDegree_f1_eval_P_le
  have hL : 2 * D.a1 + 4 * D.a2 + 6 * D.a3 =
      ∑ i ∈ D.Az, ((if D.k i = 1 then 2 else 0) + (if D.k i = 2 then 4 else 0) + (if 3 ≤ D.k i then 6 else 0)) := by
    simp only [Finset.sum_add_distrib, Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, smul_eq_mul]
    unfold KerD45Data.a1 KerD45Data.a2 KerD45Data.a3; ring
  have hR : (∑ i ∈ D.Az, (if S.isU0 i then 2 * D.k i - 1 else 2 * D.k i)) + S.a1U + S.a2U + S.a3U =
      ∑ i ∈ D.Az, ((if S.isU0 i then 2 * D.k i - 1 else 2 * D.k i) +
        (if D.k i = 1 ∧ S.isU0 i then 1 else 0) + (if D.k i = 2 ∧ S.isU0 i then 1 else 0) +
        (if 3 ≤ D.k i ∧ S.isU0 i then 1 else 0)) := by
    simp only [Finset.sum_add_distrib, Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, smul_eq_mul, mul_one]
    unfold a1U a2U a3U; ring
  have hcmp : 2 * D.a1 + 4 * D.a2 + 6 * D.a3 ≤
      (∑ i ∈ D.Az, (if S.isU0 i then 2 * D.k i - 1 else 2 * D.k i)) + S.a1U + S.a2U + S.a3U := by
    rw [hL, hR]; apply Finset.sum_le_sum; intro i _
    by_cases hU : S.isU0 i <;> simp only [hU, and_true, and_false, ↓reduceIte] <;> split_ifs <;> omega
  have hi := S.U_counts_ineqs
  have := hi.2.2.2.2.2.2.2.1; have := hi.2.2.2.2.2.2.2.2.1; have := hi.2.2.2.2.2.2.2.2.2.1
  omega

lemma aU_sum_le_UP : S.a1U + S.a2U + S.a3U ≤ S.UP.natDegree := by
  classical
  have hdvd : ∀ i ∈ D.Az, (X - C (BinaryIRSProfile.domain i)) ^ (if 1 ≤ D.k i ∧ S.isU0 i then 1 else 0) ∣ S.UP :=
    fun i hi => by
      split_ifs with h
      · rw [pow_one]; exact S.dvd_UP_of_isU0 i hi h.2
      · rw [pow_zero]; exact one_dvd _
  have hle := sum_ord_le_natDegree_of_dvd D.Az BinaryIRSProfile.domain BinaryIRSProfile.domain.injective
    S.UP S.UP_ne_zero _ hdvd
  have hsum : S.a1U + S.a2U + S.a3U = ∑ i ∈ D.Az, (if 1 ≤ D.k i ∧ S.isU0 i then 1 else 0) := by
    have hrew : S.a1U + S.a2U + S.a3U =
        ∑ i ∈ D.Az, ((if D.k i = 1 ∧ S.isU0 i then 1 else 0) + (if D.k i = 2 ∧ S.isU0 i then 1 else 0) +
          (if 3 ≤ D.k i ∧ S.isU0 i then 1 else 0)) := by
      simp only [Finset.sum_add_distrib, Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const,
        smul_eq_mul, mul_one]
      unfold a1U a2U a3U; ring
    rw [hrew]; apply Finset.sum_congr rfl; intro i _
    by_cases hU : S.isU0 i <;> simp only [hU, and_true, and_false, ↓reduceIte] <;> split_ifs <;> omega
  omega

lemma H1_U_bound : S.n1U + 3 * S.n2U + 5 * S.n3U + 2 * S.ntU ≤ S.H1.natDegree := by
  classical
  have hdvd : ∀ i ∈ (Finset.univ : Finset Idx),
      (X - C (BinaryIRSProfile.domain i)) ^ (if S.isU0 i then 2 * D.k i - 1 else 0) ∣ S.H1 := fun i _ => by
    split_ifs with hU
    · exact S.pow_dvd_H1_of_isU0 i hU
    · rw [pow_zero]; exact one_dvd _
  have hle := sum_ord_le_natDegree_of_dvd Finset.univ BinaryIRSProfile.domain BinaryIRSProfile.domain.injective
    S.H1 S.H1_ne_zero _ hdvd
  have hsum : S.n1U + 3 * S.n2U + 5 * S.n3U + 2 * S.ntU =
      ∑ i : Idx, (if S.isU0 i then 2 * D.k i - 1 else 0) := by
    have hgen : ∀ S0 : Finset Idx,
        (S0.filter fun i => D.k i = 1 ∧ S.isU0 i).card + 3 * (S0.filter fun i => D.k i = 2 ∧ S.isU0 i).card +
        5 * (S0.filter fun i => 3 ≤ D.k i ∧ S.isU0 i).card + 2 * ∑ i ∈ S0, (if S.isU0 i then D.k i - 3 else 0) =
        ∑ i ∈ S0, (if S.isU0 i then 2 * D.k i - 1 else 0) := by
      intro S0
      have hrew : (S0.filter fun i => D.k i = 1 ∧ S.isU0 i).card + 3 * (S0.filter fun i => D.k i = 2 ∧ S.isU0 i).card +
          5 * (S0.filter fun i => 3 ≤ D.k i ∧ S.isU0 i).card + 2 * ∑ i ∈ S0, (if S.isU0 i then D.k i - 3 else 0) =
          ∑ i ∈ S0, ((if D.k i = 1 ∧ S.isU0 i then 1 else 0) + (if D.k i = 2 ∧ S.isU0 i then 3 else 0) +
            (if 3 ≤ D.k i ∧ S.isU0 i then 5 else 0) + 2 * (if S.isU0 i then D.k i - 3 else 0)) := by
        simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_ite, Finset.sum_const_zero, add_zero,
          Finset.sum_const, smul_eq_mul, mul_one]; ring
      rw [hrew]; apply Finset.sum_congr rfl; intro i _
      by_cases hU : S.isU0 i <;> simp only [hU, and_true, and_false, ↓reduceIte] <;> split_ifs <;> omega
    unfold n1U n2U n3U ntU; exact hgen Finset.univ
  omega

lemma Q2_U_bound :
    (D.n1 - S.n1U) + (4 * D.n2 - 2 * S.n2U) + (8 * D.n3 - 2 * S.n3U) + 4 * D.nt ≤ S.Q2.natDegree := by
  classical
  have hdvd : ∀ i ∈ (Finset.univ : Finset Idx),
      (X - C (BinaryIRSProfile.domain i ^ 2)) ^
        (if S.isU0 i then (if D.k i ≤ 1 then 0 else 4 * D.k i - 6)
         else (if D.k i = 0 then 0 else if D.k i = 1 then 1 else 4 * D.k i - 4)) ∣ S.Q2 := fun i _ => by
    by_cases hU : S.isU0 i
    · simp only [hU, ↓reduceIte]; exact S.pow_dvd_Q2_U0 i
    · simp only [hU, ↓reduceIte]; exact S.pow_dvd_Q2_U1 i hU
  have hle := sum_ord_le_natDegree_of_dvd Finset.univ (fun i : Idx => BinaryIRSProfile.domain i ^ 2)
    domain_sq_injective S.Q2 S.Q2_ne_zero _ hdvd
  have hgen : ∀ S0 : Finset Idx,
      (S0.filter fun i => D.k i = 1).card + 4 * (S0.filter fun i => D.k i = 2).card +
      8 * (S0.filter fun i => 3 ≤ D.k i).card + 4 * ∑ i ∈ S0, (D.k i - 3) =
      (∑ i ∈ S0, (if S.isU0 i then (if D.k i ≤ 1 then 0 else 4 * D.k i - 6)
         else (if D.k i = 0 then 0 else if D.k i = 1 then 1 else 4 * D.k i - 4))) +
      (S0.filter fun i => D.k i = 1 ∧ S.isU0 i).card +
      2 * (S0.filter fun i => D.k i = 2 ∧ S.isU0 i).card +
      2 * (S0.filter fun i => 3 ≤ D.k i ∧ S.isU0 i).card := by
    intro S0
    have hL : (S0.filter fun i => D.k i = 1).card + 4 * (S0.filter fun i => D.k i = 2).card +
        8 * (S0.filter fun i => 3 ≤ D.k i).card + 4 * ∑ i ∈ S0, (D.k i - 3) =
        ∑ i ∈ S0, ((if D.k i = 1 then 1 else 0) + (if D.k i = 2 then 4 else 0) +
          (if 3 ≤ D.k i then 8 else 0) + 4 * (D.k i - 3)) := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_ite, Finset.sum_const_zero,
        add_zero, Finset.sum_const, smul_eq_mul, mul_one]; ring
    have hR : (∑ i ∈ S0, (if S.isU0 i then (if D.k i ≤ 1 then 0 else 4 * D.k i - 6)
         else (if D.k i = 0 then 0 else if D.k i = 1 then 1 else 4 * D.k i - 4))) +
        (S0.filter fun i => D.k i = 1 ∧ S.isU0 i).card +
        2 * (S0.filter fun i => D.k i = 2 ∧ S.isU0 i).card +
        2 * (S0.filter fun i => 3 ≤ D.k i ∧ S.isU0 i).card =
        ∑ i ∈ S0, ((if S.isU0 i then (if D.k i ≤ 1 then 0 else 4 * D.k i - 6)
           else (if D.k i = 0 then 0 else if D.k i = 1 then 1 else 4 * D.k i - 4)) +
          (if D.k i = 1 ∧ S.isU0 i then 1 else 0) + (if D.k i = 2 ∧ S.isU0 i then 2 else 0) +
          (if 3 ≤ D.k i ∧ S.isU0 i then 2 else 0)) := by
      simp only [Finset.sum_add_distrib, Finset.sum_ite, Finset.sum_const_zero,
        add_zero, Finset.sum_const, smul_eq_mul, mul_one]; ring
    rw [hL, hR]; apply Finset.sum_congr rfl; intro i _
    by_cases hU : S.isU0 i <;> simp only [hU, and_true, and_false, ↓reduceIte] <;> split_ifs <;> omega
  have heq : D.n1 + 4 * D.n2 + 8 * D.n3 + 4 * D.nt =
      (∑ i : Idx, (if S.isU0 i then (if D.k i ≤ 1 then 0 else 4 * D.k i - 6)
         else (if D.k i = 0 then 0 else if D.k i = 1 then 1 else 4 * D.k i - 4))) +
      S.n1U + 2 * S.n2U + 2 * S.n3U := by
    unfold n1U n2U n3U KerD45Data.n1 KerD45Data.n2 KerD45Data.n3 KerD45Data.nt
    exact hgen Finset.univ
  have hi := S.U_counts_ineqs
  have := hi.1; have := hi.2.1; have := hi.2.2.1
  omega

lemma P0_U_bound (hP0 : S.P0 ≠ 0) :
    (D.n2 + S.n2U) + (3 * D.n3 + S.n3U) + 2 * D.nt ≤ S.P0.natDegree := by
  classical
  have hdvd : ∀ i ∈ (Finset.univ : Finset Idx),
      (X - C (BinaryIRSProfile.domain i ^ 2)) ^
        (if S.isU0 i then (if D.k i ≤ 1 then 0 else 2 * D.k i - 2)
         else (if D.k i ≤ 1 then 0 else 2 * D.k i - 3)) ∣ S.P0 := fun i _ => by
    by_cases hU : S.isU0 i
    · simp only [hU, ↓reduceIte]; exact S.pow_dvd_P0_U0 i hU
    · simp only [hU, ↓reduceIte]; exact S.pow_dvd_P0_U1 i hU
  have hle := sum_ord_le_natDegree_of_dvd Finset.univ (fun i : Idx => BinaryIRSProfile.domain i ^ 2)
    domain_sq_injective S.P0 hP0 _ hdvd
  have hsum : (D.n2 + S.n2U) + (3 * D.n3 + S.n3U) + 2 * D.nt =
      ∑ i : Idx, (if S.isU0 i then (if D.k i ≤ 1 then 0 else 2 * D.k i - 2)
         else (if D.k i ≤ 1 then 0 else 2 * D.k i - 3)) := by
    have hgen : ∀ S0 : Finset Idx,
        ((S0.filter fun i => D.k i = 2).card + (S0.filter fun i => D.k i = 2 ∧ S.isU0 i).card) +
        (3 * (S0.filter fun i => 3 ≤ D.k i).card + (S0.filter fun i => 3 ≤ D.k i ∧ S.isU0 i).card) +
        2 * ∑ i ∈ S0, (D.k i - 3) =
        ∑ i ∈ S0, (if S.isU0 i then (if D.k i ≤ 1 then 0 else 2 * D.k i - 2)
           else (if D.k i ≤ 1 then 0 else 2 * D.k i - 3)) := by
      intro S0
      have hrew : ((S0.filter fun i => D.k i = 2).card + (S0.filter fun i => D.k i = 2 ∧ S.isU0 i).card) +
          (3 * (S0.filter fun i => 3 ≤ D.k i).card + (S0.filter fun i => 3 ≤ D.k i ∧ S.isU0 i).card) +
          2 * ∑ i ∈ S0, (D.k i - 3) =
          ∑ i ∈ S0, ((if D.k i = 2 then 1 else 0) + (if D.k i = 2 ∧ S.isU0 i then 1 else 0) +
            (if 3 ≤ D.k i then 3 else 0) + (if 3 ≤ D.k i ∧ S.isU0 i then 1 else 0) + 2 * (D.k i - 3)) := by
        simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_ite, Finset.sum_const_zero, add_zero,
          Finset.sum_const, smul_eq_mul, mul_one]; ring
      rw [hrew]; apply Finset.sum_congr rfl; intro i _
      by_cases hU : S.isU0 i <;> simp only [hU, and_true, and_false, ↓reduceIte] <;> split_ifs <;> omega
    unfold n2U n3U KerD45Data.n2 KerD45Data.n3 KerD45Data.nt; exact hgen Finset.univ
  omega

lemma pM10_bound_of_M21_zero (hM21 : S.M21 = 0) (hM10 : S.M10 ≠ 0) :
    2 * D.n2 + 4 * D.n3 + 2 * D.nt ≤ D.W_F - 2 * wY := by
  have hdvd : ∀ i ∈ (Finset.univ : Finset Idx),
      (X - C (BinaryIRSProfile.domain i ^ 2)) ^ (if D.k i ≤ 1 then 0 else 2 * D.k i - 2) ∣ S.p * S.M10 := by
    intro i _
    have hM10sh : S.M10sh (D.y i) = S.M10 := by unfold M10sh; rw [hM21, mul_zero, add_zero]
    rw [← hM10sh]
    exact dvd_mul_of_dvd_right (S.local_shifted_minor_ords i).1.2.2 S.p
  have hle := sum_ord_le_natDegree_of_dvd Finset.univ (fun i : Idx => BinaryIRSProfile.domain i ^ 2)
    domain_sq_injective (S.p * S.M10) (mul_ne_zero S.hp hM10) _ hdvd
  have hsum : 2 * D.n2 + 4 * D.n3 + 2 * D.nt =
      ∑ i : Idx, (if D.k i ≤ 1 then 0 else 2 * D.k i - 2) := by
    have hgen : ∀ S0 : Finset Idx,
        2 * (S0.filter fun i => D.k i = 2).card + 4 * (S0.filter fun i => 3 ≤ D.k i).card +
        2 * ∑ i ∈ S0, (D.k i - 3) = ∑ i ∈ S0, (if D.k i ≤ 1 then 0 else 2 * D.k i - 2) := by
      intro S0
      have hrew : 2 * (S0.filter fun i => D.k i = 2).card + 4 * (S0.filter fun i => 3 ≤ D.k i).card +
          2 * ∑ i ∈ S0, (D.k i - 3) =
          ∑ i ∈ S0, ((if D.k i = 2 then 2 else 0) + (if 3 ≤ D.k i then 4 else 0) + 2 * (D.k i - 3)) := by
        simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_ite, Finset.sum_const_zero, add_zero,
          Finset.sum_const, smul_eq_mul, mul_one]; ring
      rw [hrew]; apply Finset.sum_congr rfl; intro i _; split_ifs <;> omega
    unfold KerD45Data.n2 KerD45Data.n3 KerD45Data.nt; exact hgen Finset.univ
  have hdeg := S.natDegree_p_add_M10_le hM10
  rw [← natDegree_mul S.hp hM10] at hdeg
  omega

end KerD45Syzygy


end B6402Table4Common
end ProximityPrize.SubmissionBinaryLower
