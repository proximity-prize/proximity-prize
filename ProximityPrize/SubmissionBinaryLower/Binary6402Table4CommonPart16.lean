import ProximityPrize.SubmissionBinaryLower.Binary6402Table4CommonPart15
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

lemma D2_coprime_q_div_D2 : IsCoprime S.D2 (S.q / S.D2) := by
  refine isCoprime_of_forall_dvd_isUnit_poly fun d hd_D2 hd_qdiv => ?_
  have hd_q' : d ∣ S.q.derivative := by
    have hd2_q : d ^ 2 ∣ S.q := by
      rw [sq, ← EuclideanDomain.mul_div_cancel' S.D2_ne_zero S.D2_dvd_q]
      exact mul_dvd_mul hd_D2 hd_qdiv
    rcases hd2_q with ⟨w, hw⟩
    have hsq : (d ^ 2).derivative = 0 := (derivative_eq_zero_iff_sq (d ^ 2)).mpr ⟨d, rfl⟩
    rw [hw, derivative_mul, hsq, zero_mul, zero_add]
    exact dvd_mul_of_dvd_left ⟨d, sq d⟩ w.derivative
  exact S.D2_coprime_q_derivative.isUnit_of_dvd' hd_D2 hd_q'

lemma D2_rootMultiplicity_le_one (t : Fld) : S.D2.rootMultiplicity t ≤ 1 := by
  by_contra h
  have h2 : (X - C t) * (X - C t) ∣ S.D2 := by
    rw [← sq]; exact (pow_dvd_pow (X - C t) (by omega : 2 ≤ S.D2.rootMultiplicity t)).trans
      (pow_rootMultiplicity_dvd S.D2 t)
  have hu := S.D2_squarefree (X - C t) h2
  have h0 : (X - C t).natDegree = 0 := natDegree_eq_zero_of_isUnit hu
  rw [natDegree_X_sub_C] at h0; omega

lemma D1_rootMultiplicity_le_one (x : Fld) : S.D1.rootMultiplicity x ≤ 1 := by
  unfold D1; rw [rootMultiplicity_sqrtPoly S.D2 S.D2_ne_zero]; exact S.D2_rootMultiplicity_le_one (x ^ 2)

lemma dvd_of_sq_dvd_sq {a b : Fld[X]} (h : a ^ 2 ∣ b ^ 2) : a ∣ b :=
  dvd_of_sq_dvd_sq_poly h

lemma D1_dvd_R : S.D1 ∣ S.R := by
  apply dvd_of_sq_dvd_sq
  rw [S.D1_sq, ← S.q_comp_X_sq]
  rcases S.D2_dvd_q with ⟨w, hw⟩
  exact ⟨w.comp (X ^ 2), by rw [hw, mul_comp]⟩

lemma D1_dvd_UP : S.D1 ∣ S.UP := by
  unfold UP
  apply dvd_add
  · apply dvd_mul_of_dvd_left
    rcases S.D2_dvd_p with ⟨w, hw⟩
    refine ⟨S.D1 * w.comp (X ^ 2), ?_⟩
    rw [hw, mul_comp, ← S.D1_sq]; ring
  · exact S.D1_dvd_R

lemma D1_coprime_c_comp_X_sq : IsCoprime S.D1 (S.c.comp (X ^ 2)) := by
  rcases S.D2_coprime_c with ⟨u, v, huv⟩
  refine ⟨u.comp (X ^ 2) * S.D1, v.comp (X ^ 2), ?_⟩
  have hc := congrArg (fun f : Fld[X] => f.comp (X ^ 2)) huv
  simp only [add_comp, mul_comp, one_comp] at hc
  rw [← S.D1_sq] at hc
  calc u.comp (X ^ 2) * S.D1 * S.D1 + v.comp (X ^ 2) * S.c.comp (X ^ 2)
      = u.comp (X ^ 2) * S.D1 ^ 2 + v.comp (X ^ 2) * S.c.comp (X ^ 2) := by ring
    _ = 1 := hc

lemma D1_dvd_gj (j : Fin 3) : S.D1 ∣ D.gj j := by
  have heq : S.c.comp (X ^ 2) * D.gj j =
      S.p.comp (X ^ 2) * (D.Pj j).comp (X ^ 2) + S.R * (D.Bj j).comp (X ^ 2) := by
    have hsyz := congrArg (fun f : Fld[X] => f.comp (X ^ 2)) (S.hsyz j)
    simp only [add_comp, mul_comp, zero_comp] at hsyz
    have hadd := congrArg (· + S.c.comp (X ^ 2) * (D.Cj j).comp (X ^ 2)) hsyz
    have hz := CharTwo.add_self_eq_zero (S.c.comp (X ^ 2) * (D.Cj j).comp (X ^ 2))
    unfold KerD45Data.gj R
    linear_combination -hadd + hz
  have hd : S.D1 ∣ S.c.comp (X ^ 2) * D.gj j := by
    rw [heq]
    apply dvd_add
    · rcases S.D2_dvd_p with ⟨w, hw⟩
      exact ⟨S.D1 * w.comp (X ^ 2) * (D.Pj j).comp (X ^ 2), by rw [hw, mul_comp, ← S.D1_sq]; ring⟩
    · exact dvd_mul_of_dvd_left S.D1_dvd_R _
  exact S.D1_coprime_c_comp_X_sq.dvd_of_dvd_mul_left hd

lemma D1_pow5_dvd_H1 : S.D1 ^ 5 ∣ S.H1 := by
  have hD1_p : S.D1 ^ 2 ∣ S.p.comp (X ^ 2) := by
    rcases S.D2_dvd_p with ⟨w, hw⟩
    exact ⟨w.comp (X ^ 2), by rw [hw, mul_comp, S.D1_sq]⟩
  unfold H1
  apply dvd_add
  · apply dvd_add
    · have h1 : S.D1 ^ 8 ∣ S.p.comp (X ^ 2) ^ 4 := by
        rw [show (8 : ℕ) = 2 * 4 by rfl, pow_mul]; exact pow_dvd_pow_of_dvd hD1_p 4
      exact (pow_dvd_pow S.D1 (by omega : 5 ≤ 8)).trans (dvd_mul_of_dvd_left h1 _)
    · have h1 : S.D1 ^ 4 ∣ S.p.comp (X ^ 2) ^ 2 := by
        rw [show (4 : ℕ) = 2 * 2 by rfl, pow_mul]; exact pow_dvd_pow_of_dvd hD1_p 2
      have h2 : S.D1 ^ 2 ∣ S.R ^ 2 := pow_dvd_pow_of_dvd S.D1_dvd_R 2
      exact (pow_dvd_pow S.D1 (by omega : 5 ≤ 4 + 2)).trans
        (by rw [pow_add]; exact dvd_mul_of_dvd_left (mul_dvd_mul h1 h2) _)
  · rw [show (5 : ℕ) = 4 + 1 by rfl, pow_add, pow_one]
    exact mul_dvd_mul (pow_dvd_pow_of_dvd S.D1_dvd_R 4) (S.D1_dvd_gj 2)

/-! #### Pointwise `U(x_i, y_i)`, shifted minors, and exact `U = 0` vs `U ≠ 0` local orders -/

noncomputable def U_eval (i : Idx) : Fld :=
  S.p.eval (BinaryIRSProfile.domain i ^ 2) * D.y i + S.R.eval (BinaryIRSProfile.domain i)

def isU0 (i : Idx) : Prop := S.U_eval i = 0

lemma UP_eval_eq (i : Idx) (hi : i ∈ D.Az) :
    S.UP.eval (BinaryIRSProfile.domain i) = S.U_eval i := by
  unfold UP U_eval
  rw [eval_add, eval_mul, eval_comp, eval_pow, eval_X, D.hagree i hi]

lemma dvd_UP_of_isU0 (i : Idx) (hi : i ∈ D.Az) (hU : S.isU0 i) :
    X - C (BinaryIRSProfile.domain i) ∣ S.UP := by
  rw [dvd_iff_isRoot, IsRoot, S.UP_eval_eq i hi]; exact hU

lemma D2_eval_eq_zero_iff (i : Idx) :
    S.D2.eval (BinaryIRSProfile.domain i ^ 2) = 0 ↔
      S.p.eval (BinaryIRSProfile.domain i ^ 2) = 0 ∧ S.isU0 i := by
  set x0 := BinaryIRSProfile.domain i
  set t0 := x0 ^ 2
  constructor
  · intro hD2
    have hd_p : S.p.eval t0 = 0 := by
      rcases S.D2_dvd_p with ⟨w, hw⟩; rw [hw, eval_mul, hD2, zero_mul]
    have hd_q : S.q.eval t0 = 0 := by
      rcases S.D2_dvd_q with ⟨w, hw⟩; rw [hw, eval_mul, hD2, zero_mul]
    have hR0 : S.R.eval x0 = 0 := by
      have h := congrArg (Polynomial.eval x0) S.q_comp_X_sq
      rw [eval_comp, eval_pow, eval_X, hd_q, eval_pow] at h
      exact sq_eq_zero_iff.mp h.symm
    exact ⟨hd_p, by unfold isU0 U_eval; rw [hd_p, zero_mul, hR0, add_zero]⟩
  · rintro ⟨hp0, hU0⟩
    have hR0 : S.R.eval x0 = 0 := by
      unfold isU0 U_eval at hU0; rw [hp0, zero_mul, zero_add] at hU0; exact hU0
    have hq0 : S.q.eval t0 = 0 := by
      have h := congrArg (Polynomial.eval x0) S.q_comp_X_sq
      rw [eval_comp, eval_pow, eval_X, eval_pow, hR0, zero_pow (by norm_num)] at h
      exact h
    have hdvd : X - C t0 ∣ S.D2 :=
      EuclideanDomain.dvd_gcd (dvd_iff_isRoot.mpr hp0) (dvd_iff_isRoot.mpr hq0)
    exact dvd_iff_isRoot.mp hdvd

/-- Shifted linear combination `Ush x0 y0 = b + x0 c + y0 p` whose value at `t0 = x0^2` is `U(x0, y0)`. -/
noncomputable def Ush (x0 y0 : Fld) : Fld[X] := S.b + C x0 * S.c + C y0 * S.p

lemma Ush_eval (x0 y0 : Fld) :
    (S.Ush x0 y0).eval (x0 ^ 2) = S.p.eval (x0 ^ 2) * y0 + S.R.eval x0 := by
  unfold Ush R
  simp only [eval_add, eval_mul, eval_C, eval_comp, eval_pow, eval_X]
  ring

lemma shifted_syzygy (x0 y0 : Fld) (j : Fin 3) :
    S.p * D.A0sh y0 j + S.c * D.A1sh x0 y0 j + S.Ush x0 y0 * D.Bsh y0 j = 0 := by
  have h0 := S.hsyz 0; have h1 := S.hsyz 1; have h2 := S.hsyz 2
  fin_cases j
  · simp only [KerD45Data.A0sh, KerD45Data.A1sh, KerD45Data.Bsh, Ush, Fin.val_zero]
    have hz1 := CharTwo.add_self_eq_zero (C y0 * S.p * (D.Bj 0 + C (y0 ^ 2) * D.Bj 1 + C (y0 ^ 4) * D.Bj 2))
    have hz2 := CharTwo.add_self_eq_zero (C x0 * S.c * (D.Bj 0 + C (y0 ^ 2) * D.Bj 1 + C (y0 ^ 4) * D.Bj 2))
    linear_combination h0 + C (y0 ^ 2) * h1 + C (y0 ^ 4) * h2 + hz1 + hz2
  · simp only [KerD45Data.A0sh, KerD45Data.A1sh, KerD45Data.Bsh, Ush, Fin.val_one]
    have hz1 := CharTwo.add_self_eq_zero (C y0 * S.p * D.Bj 1)
    have hz2 := CharTwo.add_self_eq_zero (C x0 * S.c * D.Bj 1)
    linear_combination h1 + hz1 + hz2
  · simp only [KerD45Data.A0sh, KerD45Data.A1sh, KerD45Data.Bsh, Ush, Fin.val_two]
    have hz1 := CharTwo.add_self_eq_zero (C y0 * S.p * D.Bj 2)
    have hz2 := CharTwo.add_self_eq_zero (C x0 * S.c * D.Bj 2)
    linear_combination h2 + hz1 + hz2

lemma pow_dvd_Bsh_U1 (i : Idx) (hU : ¬ S.isU0 i) (j : Fin 3) :
    (X - C (BinaryIRSProfile.domain i ^ 2)) ^ (D.k i - j.val) ∣ D.Bsh (D.y i) j := by
  set x0 := BinaryIRSProfile.domain i
  set y0 := D.y i
  set t0 := x0 ^ 2
  have hcop : IsCoprime ((X - C t0) ^ (D.k i - j.val)) (S.Ush x0 y0) := by
    apply IsCoprime.pow_left
    have hne : (S.Ush x0 y0).eval t0 ≠ 0 := by rw [S.Ush_eval]; exact hU
    exact (Polynomial.irreducible_X_sub_C t0).coprime_iff_not_dvd.mpr (mt dvd_iff_isRoot.mp hne)
  have hdvd : (X - C t0) ^ (D.k i - j.val) ∣ S.Ush x0 y0 * D.Bsh y0 j := by
    have hsyz := S.shifted_syzygy x0 y0 j
    have heq : S.Ush x0 y0 * D.Bsh y0 j = S.p * D.A0sh y0 j + S.c * D.A1sh x0 y0 j := by
      have hadd := congrArg (· + S.Ush x0 y0 * D.Bsh y0 j) hsyz
      have hz := CharTwo.add_self_eq_zero (S.Ush x0 y0 * D.Bsh y0 j)
      linear_combination -hadd + hz
    rw [heq]
    exact dvd_add (dvd_mul_of_dvd_right (D.local_shifted_ords i j).1 S.p)
      (dvd_mul_of_dvd_right (D.local_shifted_ords i j).2.1 S.c)
  exact hcop.dvd_of_dvd_mul_left hdvd

theorem pow_dvd_ResY_U1 (i : Idx) (hU : ¬ S.isU0 i) :
    (X - C (BinaryIRSProfile.domain i)) ^ KerD45Data.resOrdU1 (D.k i) ∣ D.ResY := by
  simpa only [show (1 : ℕ) ≠ 0 by omega, ↓reduceIte] using
    D.pow_dvd_ResY_general i 1 (by omega) fun j => S.pow_dvd_Bsh_U1 i hU j

theorem pow_dvd_f1_eval_P_U1 (i : Idx) (hi : i ∈ D.Az) (hU : ¬ S.isU0 i) :
    (X - C (BinaryIRSProfile.domain i)) ^ (2 * D.k i) ∣ D.f1.eval D.P := by
  set x0 := BinaryIRSProfile.domain i
  set y0 := D.y i
  set t0 := x0 ^ 2
  have hP0 : D.P.eval x0 = y0 := D.hagree i hi
  have hm1 : biMultGE x0 y0 D.f1 (2 * D.k i) := by
    intro a b hab
    rw [D.shiftBi_f1_eq x0 y0, finset_sum_coeff, finset_sum_coeff]
    apply Finset.sum_eq_zero; intro j _
    rw [coeff_C_mul_X_pow]
    split_ifs with hb
    · rw [coeff_even_odd_pair]
      split_ifs with ha
      · exact shift_coeff_zero_of_pow_dvd _ t0 _ (D.local_shifted_ords i j).2.1 (a / 2) (by omega)
      · exact shift_coeff_zero_of_pow_dvd _ t0 _ (S.pow_dvd_Bsh_U1 i hU j) (a / 2) (by omega)
    · simp
  apply pow_dvd_of_shift_coeff_zero _ x0 _
  have hsh : (D.f1.eval D.P).comp (C x0 + X) =
      (shiftBi x0 y0 D.f1).eval (D.P.comp (C x0 + X) - C y0) := by
    unfold shiftBi
    rw [Polynomial.eval_comp, eval_add, eval_C, eval_X, add_sub_cancel]
    exact (Polynomial.eval_map_apply (f := Polynomial.compRingHom (C x0 + X)) (x := D.P) (p := D.f1)).symm
  rw [hsh]
  have hPsh_dvd : X ∣ (D.P.comp (C x0 + X) - C y0) := by
    rw [X_dvd_iff, coeff_sub, coeff_zero_eq_eval_zero, eval_comp, eval_add, eval_C, eval_X, add_zero,
      coeff_C_zero, hP0, sub_self]
  set Q := D.P.comp (C x0 + X) - C y0
  have hdvd_tot : X ^ (2 * D.k i) ∣ (shiftBi x0 y0 D.f1).eval Q := by
    rw [eval_eq_sum_range]
    apply Finset.dvd_sum; intro j _
    have hcj : X ^ (2 * D.k i - j) ∣ (shiftBi x0 y0 D.f1).coeff j := by
      simpa only [one_mul] using (biMultGE_iff_weightedOrdGE_one x0 y0 D.f1 (2 * D.k i)).mp hm1 j
    have hQj : X ^ j ∣ Q ^ j := pow_dvd_pow_of_dvd hPsh_dvd j
    exact (pow_dvd_pow X (show 2 * D.k i ≤ (2 * D.k i - j) + j by omega)).trans
      (by rw [pow_add]; exact mul_dvd_mul hcj hQj)
  exact X_pow_dvd_iff.mp hdvd_tot

noncomputable def M20sh (y0 : Fld) : Fld[X] := S.M20 + C (y0 ^ 2) * S.M21
noncomputable def M10sh (y0 : Fld) : Fld[X] := S.M10 + C (y0 ^ 4) * S.M21

lemma shifted_minor_identities (x0 y0 : Fld) :
    (S.p * S.M21 = D.A1sh x0 y0 2 * D.Bsh y0 1 + D.A1sh x0 y0 1 * D.Bsh y0 2 ∧
     S.c * S.M21 = D.A0sh y0 2 * D.Bsh y0 1 + D.A0sh y0 1 * D.Bsh y0 2 ∧
     S.Ush x0 y0 * S.M21 = D.A0sh y0 2 * D.A1sh x0 y0 1 + D.A0sh y0 1 * D.A1sh x0 y0 2) ∧
    (S.p * S.M20sh y0 = D.A1sh x0 y0 2 * D.Bsh y0 0 + D.A1sh x0 y0 0 * D.Bsh y0 2 ∧
     S.c * S.M20sh y0 = D.A0sh y0 2 * D.Bsh y0 0 + D.A0sh y0 0 * D.Bsh y0 2 ∧
     S.Ush x0 y0 * S.M20sh y0 = D.A0sh y0 2 * D.A1sh x0 y0 0 + D.A0sh y0 0 * D.A1sh x0 y0 2) ∧
    (S.p * S.M10sh y0 = D.A1sh x0 y0 1 * D.Bsh y0 0 + D.A1sh x0 y0 0 * D.Bsh y0 1 ∧
     S.c * S.M10sh y0 = D.A0sh y0 1 * D.Bsh y0 0 + D.A0sh y0 0 * D.Bsh y0 1 ∧
     S.Ush x0 y0 * S.M10sh y0 = D.A0sh y0 1 * D.A1sh x0 y0 0 + D.A0sh y0 0 * D.A1sh x0 y0 1) :=
  shifted_minor_identities_ring S.p S.c S.b (C x0) (C y0) (C (y0 ^ 2)) (C (y0 ^ 4))
    (D.Pj 0) (D.Pj 1) (D.Pj 2) (D.Cj 0) (D.Cj 1) (D.Cj 2) (D.Bj 0) (D.Bj 1) (D.Bj 2)
    S.M21 S.M20 S.M10
    S.p_mul_M21 S.c_mul_M21 S.b_mul_M21 S.p_mul_M20 S.c_mul_M20 S.b_mul_M20 S.p_mul_M10 S.c_mul_M10 S.b_mul_M10

lemma pow_dvd_of_coprime_triple {x0 y0 t0 : Fld} {m : ℕ} {M : Fld[X]}
    (hp : (X - C t0) ^ m ∣ S.p * M) (hc : (X - C t0) ^ m ∣ S.c * M)
    (hu : (X - C t0) ^ m ∣ S.Ush x0 y0 * M) : (X - C t0) ^ m ∣ M := by
  have hne : S.p.eval t0 ≠ 0 ∨ S.c.eval t0 ≠ 0 ∨ (S.Ush x0 y0).eval t0 ≠ 0 := by
    by_contra hall; push Not at hall
    have hdp : X - C t0 ∣ S.p := dvd_iff_isRoot.mpr hall.1
    have hdc : X - C t0 ∣ S.c := dvd_iff_isRoot.mpr hall.2.1
    have hdu : X - C t0 ∣ S.Ush x0 y0 := dvd_iff_isRoot.mpr hall.2.2
    have hdb : X - C t0 ∣ S.b := by
      have hb_eq : S.b = S.Ush x0 y0 + C x0 * S.c + C y0 * S.p := by
        unfold Ush
        have z1 := CharTwo.add_self_eq_zero (C x0 * S.c)
        have z2 := CharTwo.add_self_eq_zero (C y0 * S.p)
        linear_combination -z1 - z2
      rw [hb_eq]; exact dvd_add (dvd_add hdu (dvd_mul_of_dvd_right hdc _)) (dvd_mul_of_dvd_right hdp _)
    have hu1 := S.hcop (X - C t0) hdp hdc hdb
    have hdeg := natDegree_eq_zero_of_isUnit hu1
    rw [natDegree_X_sub_C] at hdeg; omega
  rcases hne with h | h | h
  · exact ((Polynomial.irreducible_X_sub_C t0).coprime_iff_not_dvd.mpr (mt dvd_iff_isRoot.mp h)).pow_left.dvd_of_dvd_mul_left hp
  · exact ((Polynomial.irreducible_X_sub_C t0).coprime_iff_not_dvd.mpr (mt dvd_iff_isRoot.mp h)).pow_left.dvd_of_dvd_mul_left hc
  · exact ((Polynomial.irreducible_X_sub_C t0).coprime_iff_not_dvd.mpr (mt dvd_iff_isRoot.mp h)).pow_left.dvd_of_dvd_mul_left hu

/-- Exact local `T`-orders of `M21`, `M20sh`, `M10sh` at EVERY point `i : Idx` (both `U = 0` and `U ≠ 0`)! -/
theorem local_shifted_minor_ords (i : Idx) :
    let t0 : Fld := BinaryIRSProfile.domain i ^ 2
    let k := D.k i
    ((X - C t0) ^ (2 * k - 4) ∣ S.M21 ∧
     (X - C t0) ^ (if k ≤ 1 then 0 else 2 * k - 3) ∣ S.M20sh (D.y i) ∧
     (X - C t0) ^ (if k ≤ 1 then 0 else 2 * k - 2) ∣ S.M10sh (D.y i)) ∧
    (¬ S.isU0 i →
      (X - C t0) ^ (if k ≤ 1 then 0 else 2 * k - 3) ∣ S.M21 ∧
      (X - C t0) ^ (if k = 0 then 0 else if k = 1 then 1 else 2 * k - 2) ∣ S.M20sh (D.y i) ∧
      (X - C t0) ^ (if k = 0 then 0 else 2 * k - 1) ∣ S.M10sh (D.y i)) := by
  intro t0 k
  set x0 := BinaryIRSProfile.domain i
  set y0 := D.y i
  have hloc0 := D.local_shifted_ords i 0
  have hloc1 := D.local_shifted_ords i 1
  have hloc2 := D.local_shifted_ords i 2
  have ⟨⟨hp21, hc21, hu21⟩, ⟨hp20, hc20, hu20⟩, ⟨hp10, hc10, hu10⟩⟩ := S.shifted_minor_identities x0 y0
  have hU_cop : ¬ S.isU0 i → ∀ m : ℕ, IsCoprime ((X - C t0) ^ m) (S.Ush x0 y0) := fun hU m => by
    apply IsCoprime.pow_left
    have hne : (S.Ush x0 y0).eval t0 ≠ 0 := by rw [S.Ush_eval]; exact hU
    exact (Polynomial.irreducible_X_sub_C t0).coprime_iff_not_dvd.mpr (mt dvd_iff_isRoot.mp hne)
  have hmul_ord : ∀ {a b m : ℕ} {f g : Fld[X]}, m ≤ a + b →
      (X - C t0) ^ a ∣ f → (X - C t0) ^ b ∣ g → (X - C t0) ^ m ∣ f * g := fun hle hf hg =>
    (pow_dvd_pow (X - C t0) hle).trans (by rw [pow_add]; exact mul_dvd_mul hf hg)
  have hu21_d : (X - C t0) ^ (if k ≤ 1 then 0 else 2 * k - 3) ∣ S.Ush x0 y0 * S.M21 := by
    rw [hu21]; exact dvd_add (hmul_ord (by split_ifs <;> omega) hloc2.1 hloc1.2.1)
      (hmul_ord (by split_ifs <;> omega) hloc1.1 hloc2.2.1)
  have hu20_d : (X - C t0) ^ (if k = 0 then 0 else if k = 1 then 1 else 2 * k - 2) ∣ S.Ush x0 y0 * S.M20sh y0 := by
    rw [hu20]; exact dvd_add (hmul_ord (by split_ifs <;> omega) hloc2.1 hloc0.2.1)
      (hmul_ord (by split_ifs <;> omega) hloc0.1 hloc2.2.1)
  have hu10_d : (X - C t0) ^ (if k = 0 then 0 else 2 * k - 1) ∣ S.Ush x0 y0 * S.M10sh y0 := by
    rw [hu10]; exact dvd_add (hmul_ord (by split_ifs <;> omega) hloc1.1 hloc0.2.1)
      (hmul_ord (by split_ifs <;> omega) hloc0.1 hloc1.2.1)
  refine ⟨⟨?_, ?_, ?_⟩, fun hU => ⟨(hU_cop hU _).dvd_of_dvd_mul_left hu21_d,
    (hU_cop hU _).dvd_of_dvd_mul_left hu20_d, (hU_cop hU _).dvd_of_dvd_mul_left hu10_d⟩⟩
  · apply S.pow_dvd_of_coprime_triple (x0 := x0) (y0 := y0)
    · rw [hp21]; exact dvd_add (hmul_ord (by omega) hloc2.2.1 hloc1.2.2) (hmul_ord (by omega) hloc1.2.1 hloc2.2.2)
    · rw [hc21]; exact dvd_add (hmul_ord (by omega) hloc2.1 hloc1.2.2) (hmul_ord (by omega) hloc1.1 hloc2.2.2)
    · exact (pow_dvd_pow (X - C t0) (by split_ifs <;> omega)).trans hu21_d
  · apply S.pow_dvd_of_coprime_triple (x0 := x0) (y0 := y0)
    · rw [hp20]; exact dvd_add (hmul_ord (by split_ifs <;> omega) hloc2.2.1 hloc0.2.2)
        (hmul_ord (by split_ifs <;> omega) hloc0.2.1 hloc2.2.2)
    · rw [hc20]; exact dvd_add (hmul_ord (by split_ifs <;> omega) hloc2.1 hloc0.2.2)
        (hmul_ord (by split_ifs <;> omega) hloc0.1 hloc2.2.2)
    · exact (pow_dvd_pow (X - C t0) (by split_ifs <;> omega)).trans hu20_d
  · apply S.pow_dvd_of_coprime_triple (x0 := x0) (y0 := y0)
    · rw [hp10]; exact dvd_add (hmul_ord (by split_ifs <;> omega) hloc1.2.1 hloc0.2.2)
        (hmul_ord (by split_ifs <;> omega) hloc0.2.1 hloc1.2.2)
    · rw [hc10]; exact dvd_add (hmul_ord (by split_ifs <;> omega) hloc1.1 hloc0.2.2)
        (hmul_ord (by split_ifs <;> omega) hloc0.1 hloc1.2.2)
    · exact (pow_dvd_pow (X - C t0) (by split_ifs <;> omega)).trans hu10_d

lemma Q2_eq_shifted (y0 : Fld) : S.Q2 = (S.M20sh y0) ^ 2 + S.M21 * S.M10sh y0 := by
  unfold Q2 M20sh M10sh
  have h2 : (2 : Fld[X]) = 0 := CharTwo.two_eq_zero
  have hz := CharTwo.add_self_eq_zero (C (y0 ^ 4) * S.M21 ^ 2)
  have hsq : C (y0 ^ 2) ^ 2 = (C (y0 ^ 4) : Fld[X]) := by rw [← map_pow, show (y0 ^ 2) ^ 2 = y0 ^ 4 by ring]
  calc S.M20 ^ 2 + S.M21 * S.M10
      = S.M20 ^ 2 + 2 * S.M20 * (C (y0 ^ 2) * S.M21) + C (y0 ^ 2) ^ 2 * S.M21 ^ 2 +
        S.M21 * S.M10 + C (y0 ^ 4) * S.M21 ^ 2 := by rw [h2, hsq]; linear_combination -hz
    _ = (S.M20 + C (y0 ^ 2) * S.M21) ^ 2 + S.M21 * (S.M10 + C (y0 ^ 4) * S.M21) := by ring

lemma P0_eq_shifted (y0 : Fld) :
    S.P0 = S.p ^ 4 * S.M10sh y0 + (S.q + C (y0 ^ 2) * S.p ^ 2) ^ 2 * S.M21 := by
  unfold P0 M10sh
  have h2 : (2 : Fld[X]) = 0 := CharTwo.two_eq_zero
  have hz := CharTwo.add_self_eq_zero (C (y0 ^ 4) * S.p ^ 4 * S.M21)
  have hsq : C (y0 ^ 2) ^ 2 = (C (y0 ^ 4) : Fld[X]) := by rw [← map_pow, show (y0 ^ 2) ^ 2 = y0 ^ 4 by ring]
  calc S.p ^ 4 * S.M10 + S.q ^ 2 * S.M21
      = S.p ^ 4 * S.M10 + C (y0 ^ 4) * S.p ^ 4 * S.M21 +
        (S.q ^ 2 + 2 * S.q * (C (y0 ^ 2) * S.p ^ 2) + C (y0 ^ 2) ^ 2 * S.p ^ 4) * S.M21 := by
          rw [h2, hsq]; linear_combination -hz
    _ = S.p ^ 4 * (S.M10 + C (y0 ^ 4) * S.M21) + (S.q + C (y0 ^ 2) * S.p ^ 2) ^ 2 * S.M21 := by ring

lemma pow_dvd_Q2_U0 (i : Idx) :
    (X - C (BinaryIRSProfile.domain i ^ 2)) ^ (if D.k i ≤ 1 then 0 else 4 * D.k i - 6) ∣ S.Q2 := by
  rw [S.Q2_eq_shifted (D.y i)]
  have ⟨h21, h20, h10⟩ := (S.local_shifted_minor_ords i).1
  apply dvd_add
  · refine (pow_dvd_pow _ (show (if D.k i ≤ 1 then 0 else 4 * D.k i - 6) ≤
        2 * (if D.k i ≤ 1 then 0 else 2 * D.k i - 3) by split_ifs <;> omega)).trans ?_
    rw [show 2 * (if D.k i ≤ 1 then 0 else 2 * D.k i - 3) = (if D.k i ≤ 1 then 0 else 2 * D.k i - 3) * 2 by ring, pow_mul]
    exact pow_dvd_pow_of_dvd h20 2
  · refine (pow_dvd_pow _ (show (if D.k i ≤ 1 then 0 else 4 * D.k i - 6) ≤
        (2 * D.k i - 4) + (if D.k i ≤ 1 then 0 else 2 * D.k i - 2) by split_ifs <;> omega)).trans ?_
    rw [pow_add]; exact mul_dvd_mul h21 h10

lemma pow_dvd_Q2_U1 (i : Idx) (hU : ¬ S.isU0 i) :
    (X - C (BinaryIRSProfile.domain i ^ 2)) ^
      (if D.k i = 0 then 0 else if D.k i = 1 then 1 else 4 * D.k i - 4) ∣ S.Q2 := by
  rw [S.Q2_eq_shifted (D.y i)]
  have ⟨h21, h20, h10⟩ := (S.local_shifted_minor_ords i).2 hU
  apply dvd_add
  · refine (pow_dvd_pow _ (show (if D.k i = 0 then 0 else if D.k i = 1 then 1 else 4 * D.k i - 4) ≤
        2 * (if D.k i = 0 then 0 else if D.k i = 1 then 1 else 2 * D.k i - 2) by split_ifs <;> omega)).trans ?_
    rw [show 2 * (if D.k i = 0 then 0 else if D.k i = 1 then 1 else 2 * D.k i - 2) =
        (if D.k i = 0 then 0 else if D.k i = 1 then 1 else 2 * D.k i - 2) * 2 by ring, pow_mul]
    exact pow_dvd_pow_of_dvd h20 2
  · refine (pow_dvd_pow _ (show (if D.k i = 0 then 0 else if D.k i = 1 then 1 else 4 * D.k i - 4) ≤
        (if D.k i ≤ 1 then 0 else 2 * D.k i - 3) + (if D.k i = 0 then 0 else 2 * D.k i - 1) by split_ifs <;> omega)).trans ?_
    rw [pow_add]; exact mul_dvd_mul h21 h10

lemma pow_dvd_P0_U0 (i : Idx) (hU : S.isU0 i) :
    (X - C (BinaryIRSProfile.domain i ^ 2)) ^ (if D.k i ≤ 1 then 0 else 2 * D.k i - 2) ∣ S.P0 := by
  set x0 := BinaryIRSProfile.domain i
  set y0 := D.y i
  set t0 := x0 ^ 2
  rw [S.P0_eq_shifted y0]
  have ⟨h21, _, h10⟩ := (S.local_shifted_minor_ords i).1
  have hqsh : X - C t0 ∣ S.q + C (y0 ^ 2) * S.p ^ 2 := by
    rw [dvd_iff_isRoot, IsRoot, eval_add, eval_mul, eval_C, eval_pow]
    have hqval : S.q.eval t0 = S.R.eval x0 ^ 2 := by
      have h := congrArg (Polynomial.eval x0) S.q_comp_X_sq
      simpa [eval_comp, eval_pow, eval_X] using h
    rw [hqval]
    have h2 : (2 : Fld) = 0 := CharTwo.two_eq_zero
    calc S.R.eval x0 ^ 2 + y0 ^ 2 * S.p.eval t0 ^ 2
        = (S.p.eval t0 * y0 + S.R.eval x0) ^ 2 - 2 * (S.p.eval t0 * y0) * S.R.eval x0 := by ring
      _ = S.U_eval i ^ 2 := by rw [h2]; unfold U_eval; ring
      _ = 0 := by rw [hU]; ring
  apply dvd_add
  · exact dvd_mul_of_dvd_right h10 _
  · exact (pow_dvd_pow _ (show (if D.k i ≤ 1 then 0 else 2 * D.k i - 2) ≤ 2 + (2 * D.k i - 4) by split_ifs <;> omega)).trans
      (by rw [pow_add]; exact mul_dvd_mul (pow_dvd_pow_of_dvd hqsh 2) h21)

lemma pow_dvd_P0_U1 (i : Idx) (hU : ¬ S.isU0 i) :
    (X - C (BinaryIRSProfile.domain i ^ 2)) ^ (if D.k i ≤ 1 then 0 else 2 * D.k i - 3) ∣ S.P0 := by
  rw [S.P0_eq_shifted (D.y i)]
  have ⟨h21, _, h10⟩ := (S.local_shifted_minor_ords i).2 hU
  apply dvd_add
  · exact dvd_mul_of_dvd_right ((pow_dvd_pow _ (by split_ifs <;> omega)).trans h10) _
  · exact dvd_mul_of_dvd_right h21 _

lemma pow_dvd_H1_of_isU0 (i : Idx) (hU : S.isU0 i) :
    (X - C (BinaryIRSProfile.domain i)) ^ (2 * D.k i - 1) ∣ S.H1 := by
  set x0 := BinaryIRSProfile.domain i
  set y0 := D.y i
  set t0 := x0 ^ 2
  set Uy0 : Fld[X] := S.p.comp (X ^ 2) * C y0 + S.R
  have hUy0 : X - C x0 ∣ Uy0 := by
    rw [dvd_iff_isRoot, IsRoot]
    simp only [Uy0, eval_add, eval_mul, eval_comp, eval_pow, eval_X, eval_C]
    exact hU
  have hH1_rew : S.H1 =
      S.p.comp (X ^ 2) ^ 4 * (D.gj 0 + C (y0 ^ 2) * D.gj 1 + C (y0 ^ 4) * D.gj 2) +
      S.p.comp (X ^ 2) ^ 2 * Uy0 ^ 2 * D.gj 1 + Uy0 ^ 4 * D.gj 2 := by
    have h2 : (2 : Fld[X]) = 0 := CharTwo.two_eq_zero
    have hR : S.R = Uy0 + S.p.comp (X ^ 2) * C y0 := by
      dsimp [Uy0]; rw [add_assoc, add_comm S.R, ← add_assoc, CharTwo.add_self_eq_zero, zero_add]
    have hR2 : S.R ^ 2 = Uy0 ^ 2 + S.p.comp (X ^ 2) ^ 2 * C (y0 ^ 2) := by
      rw [hR]; calc (Uy0 + S.p.comp (X ^ 2) * C y0) ^ 2
          = Uy0 ^ 2 + 2 * Uy0 * (S.p.comp (X ^ 2) * C y0) + S.p.comp (X ^ 2) ^ 2 * C y0 ^ 2 := by ring
        _ = Uy0 ^ 2 + S.p.comp (X ^ 2) ^ 2 * C (y0 ^ 2) := by rw [h2, ← map_pow]; ring
    have hR4 : S.R ^ 4 = Uy0 ^ 4 + S.p.comp (X ^ 2) ^ 4 * C (y0 ^ 4) := by
      calc S.R ^ 4 = (S.R ^ 2) ^ 2 := by ring
        _ = (Uy0 ^ 2 + S.p.comp (X ^ 2) ^ 2 * C (y0 ^ 2)) ^ 2 := by rw [hR2]
        _ = Uy0 ^ 4 + 2 * Uy0 ^ 2 * (S.p.comp (X ^ 2) ^ 2 * C (y0 ^ 2)) +
              S.p.comp (X ^ 2) ^ 4 * C (y0 ^ 2) ^ 2 := by ring
        _ = Uy0 ^ 4 + S.p.comp (X ^ 2) ^ 4 * C (y0 ^ 4) := by
              rw [h2, ← map_pow, show (y0 ^ 2) ^ 2 = y0 ^ 4 by ring]; ring
    unfold H1; rw [hR2, hR4]; ring
  have hgsh_dvd : ∀ (j : Fin 3) (gsh : Fld[X]),
      gsh = (D.A1sh x0 y0 j).comp (X ^ 2) + (X - C x0) * (D.Bsh y0 j).comp (X ^ 2) →
      (X - C x0) ^ (2 * D.k i - 1 - 2 * j.val) ∣ gsh := by
    intro j gsh hgsh
    rw [hgsh]
    have hloc := D.local_shifted_ords i j
    apply dvd_add
    · exact (pow_dvd_pow (X - C x0) (by omega : 2 * D.k i - 1 - 2 * j.val ≤ 2 * (D.k i - j.val))).trans
        ((pow_dvd_comp_X_sq_iff _ x0 _).mpr hloc.2.1)
    · by_cases hpos : 2 * D.k i - 1 - 2 * j.val = 0
      · rw [hpos, pow_zero]; exact one_dvd _
      · exact (pow_dvd_pow (X - C x0) (by omega : 2 * D.k i - 1 - 2 * j.val ≤ 1 + 2 * (D.k i - 1 - j.val))).trans
          (by rw [pow_add, pow_one]; exact mul_dvd_mul dvd_rfl ((pow_dvd_comp_X_sq_iff _ x0 _).mpr hloc.2.2))
  have hg0d : (X - C x0) ^ (2 * D.k i - 1) ∣ D.gj 0 + C (y0 ^ 2) * D.gj 1 + C (y0 ^ 4) * D.gj 2 := by
    simpa only [Fin.val_zero, mul_zero, Nat.sub_zero] using hgsh_dvd 0 _ (by
      simp only [KerD45Data.gj, KerD45Data.A1sh, KerD45Data.Bsh, Fin.val_zero, add_comp, mul_comp, C_comp]; ring)
  have hg1d : (X - C x0) ^ (2 * D.k i - 3) ∣ D.gj 1 := by
    simpa only [Fin.val_one, mul_one, Nat.sub_sub] using hgsh_dvd 1 _ (by
      simp only [KerD45Data.gj, KerD45Data.A1sh, KerD45Data.Bsh, Fin.val_one, add_comp, mul_comp, C_comp]; ring)
  have hg2d : (X - C x0) ^ (2 * D.k i - 5) ∣ D.gj 2 := D.pow_dvd_g2_of_k i
  rw [hH1_rew]
  apply dvd_add
  · apply dvd_add
    · exact dvd_mul_of_dvd_right hg0d _
    · rw [mul_assoc]
      exact dvd_mul_of_dvd_right ((pow_dvd_pow (X - C x0) (by omega : 2 * D.k i - 1 ≤ 2 + (2 * D.k i - 3))).trans
        (by rw [pow_add]; exact mul_dvd_mul (pow_dvd_pow_of_dvd hUy0 2) hg1d)) _
  · exact (pow_dvd_pow (X - C x0) (by omega : 2 * D.k i - 1 ≤ 4 + (2 * D.k i - 5))).trans
      (by rw [pow_add]; exact mul_dvd_mul (pow_dvd_pow_of_dvd hUy0 4) hg2d)

/-! #### Shared `U = 0` point counts (`n1U, n2U, n3U, ntU, a1U, a2U, a3U`) and universal sum bounds -/

noncomputable def n1U : ℕ := by
  classical exact (Finset.univ.filter fun i : Idx => D.k i = 1 ∧ S.isU0 i).card
noncomputable def n2U : ℕ := by
  classical exact (Finset.univ.filter fun i : Idx => D.k i = 2 ∧ S.isU0 i).card
noncomputable def n3U : ℕ := by
  classical exact (Finset.univ.filter fun i : Idx => 3 ≤ D.k i ∧ S.isU0 i).card
noncomputable def ntU : ℕ := by
  classical exact ∑ i : Idx, if S.isU0 i then D.k i - 3 else 0
noncomputable def a1U : ℕ := by
  classical exact (D.Az.filter fun i : Idx => D.k i = 1 ∧ S.isU0 i).card
noncomputable def a2U : ℕ := by
  classical exact (D.Az.filter fun i : Idx => D.k i = 2 ∧ S.isU0 i).card
noncomputable def a3U : ℕ := by
  classical exact (D.Az.filter fun i : Idx => 3 ≤ D.k i ∧ S.isU0 i).card

attribute [irreducible] n1U n2U n3U ntU a1U a2U a3U

lemma U_counts_ineqs :
    S.n1U ≤ D.n1 ∧ S.n2U ≤ D.n2 ∧ S.n3U ≤ D.n3 ∧ S.ntU ≤ D.nt ∧
    S.a1U ≤ S.n1U ∧ S.a2U ≤ S.n2U ∧ S.a3U ≤ S.n3U ∧
    S.a1U ≤ D.a1 ∧ S.a2U ≤ D.a2 ∧ S.a3U ≤ D.a3 ∧
    D.a1 + S.n1U ≤ D.n1 + S.a1U ∧ D.a2 + S.n2U ≤ D.n2 + S.a2U ∧ D.a3 + S.n3U ≤ D.n3 + S.a3U := by
  classical
  have hsub : ∀ (U : Finset Idx) (hAU : D.Az ⊆ U) (p q : Idx → Prop) [DecidablePred p] [DecidablePred q],
      (D.Az.filter fun i => p i ∧ q i).card ≤ (U.filter fun i => p i ∧ q i).card ∧
      (D.Az.filter fun i => p i ∧ q i).card ≤ (D.Az.filter p).card ∧
      (U.filter fun i => p i ∧ q i).card ≤ (U.filter p).card ∧
      (D.Az.filter p).card + (U.filter fun i => p i ∧ q i).card ≤
        (U.filter p).card + (D.Az.filter fun i => p i ∧ q i).card := by
    intro U hAU p q _ _
    have h1 : (D.Az.filter fun i => p i ∧ q i) ⊆ (U.filter fun i => p i ∧ q i) :=
      Finset.filter_subset_filter _ hAU
    have h2 : (D.Az.filter fun i => p i ∧ q i) ⊆ (D.Az.filter p) := fun i hi => by
      simp only [Finset.mem_filter] at hi ⊢; exact ⟨hi.1, hi.2.1⟩
    have h3 : (U.filter fun i => p i ∧ q i) ⊆ (U.filter p) := fun i hi => by
      simp only [Finset.mem_filter] at hi ⊢; exact ⟨hi.1, hi.2.1⟩
    have h4 : (D.Az.filter p).card - (D.Az.filter fun i => p i ∧ q i).card ≤
        (U.filter p).card - (U.filter fun i => p i ∧ q i).card := by
      have hs1 : (D.Az.filter p) \ (D.Az.filter fun i => p i ∧ q i) ⊆
          (U.filter p) \ (U.filter fun i => p i ∧ q i) := fun i hi => by
        simp only [Finset.mem_sdiff, Finset.mem_filter] at hi ⊢
        exact ⟨⟨hAU hi.1.1, hi.1.2⟩, fun h => hi.2 ⟨hi.1.1, h.2⟩⟩
      have hc := Finset.card_le_card hs1
      rw [Finset.card_sdiff_of_subset h2, Finset.card_sdiff_of_subset h3] at hc
      exact hc
    have hc2 := Finset.card_le_card h2
    have hc3 := Finset.card_le_card h3
    exact ⟨Finset.card_le_card h1, hc2, hc3, by omega⟩
  have s1 := hsub Finset.univ (Finset.subset_univ _) (fun i => D.k i = 1) S.isU0
  have s2 := hsub Finset.univ (Finset.subset_univ _) (fun i => D.k i = 2) S.isU0
  have s3 := hsub Finset.univ (Finset.subset_univ _) (fun i => 3 ≤ D.k i) S.isU0
  have hnt : S.ntU ≤ D.nt := by
    unfold ntU KerD45Data.nt
    apply Finset.sum_le_sum; intro i _; split_ifs <;> omega
  unfold n1U n2U n3U a1U a2U a3U KerD45Data.n1 KerD45Data.n2 KerD45Data.n3 KerD45Data.a1 KerD45Data.a2 KerD45Data.a3
  refine ⟨?_, ?_, ?_, hnt, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact s1.2.2.1
  · exact s2.2.2.1
  · exact s3.2.2.1
  · exact s1.1
  · exact s2.1
  · exact s3.1
  · exact s1.2.1
  · exact s2.2.1
  · exact s3.2.1
  · exact s1.2.2.2
  · exact s2.2.2.2
  · exact s3.2.2.2

lemma ResY_U_bound :
    (4 * D.n1 - 3 * S.n1U) + (16 * D.n2 - 5 * S.n2U) + (34 * D.n3 - 5 * S.n3U) + 18 * D.nt ≤
      D.ResY.natDegree := by
  classical
  have hdvd : ∀ i ∈ (Finset.univ : Finset Idx),
      (X - C (BinaryIRSProfile.domain i)) ^
        (if S.isU0 i then KerD45Data.resOrdU0 (D.k i) else KerD45Data.resOrdU1 (D.k i)) ∣ D.ResY := fun i _ => by
    split_ifs with hU
    · exact D.pow_dvd_ResY_U0 i
    · exact S.pow_dvd_ResY_U1 i hU
  have hle := sum_ord_le_natDegree_of_dvd Finset.univ BinaryIRSProfile.domain
    BinaryIRSProfile.domain.injective D.ResY D.ResY_ne_zero _ hdvd
  have hgen : ∀ S0 : Finset Idx,
      4 * (S0.filter fun i => D.k i = 1).card + 16 * (S0.filter fun i => D.k i = 2).card +
      34 * (S0.filter fun i => 3 ≤ D.k i).card + 18 * ∑ i ∈ S0, (D.k i - 3) =
      (∑ i ∈ S0, (if S.isU0 i then KerD45Data.resOrdU0 (D.k i) else KerD45Data.resOrdU1 (D.k i))) +
      3 * (S0.filter fun i => D.k i = 1 ∧ S.isU0 i).card +
      5 * (S0.filter fun i => D.k i = 2 ∧ S.isU0 i).card +
      5 * (S0.filter fun i => 3 ≤ D.k i ∧ S.isU0 i).card := by
    intro S0
    have hL : 4 * (S0.filter fun i => D.k i = 1).card + 16 * (S0.filter fun i => D.k i = 2).card +
        34 * (S0.filter fun i => 3 ≤ D.k i).card + 18 * ∑ i ∈ S0, (D.k i - 3) =
        ∑ i ∈ S0, ((if D.k i = 1 then 4 else 0) + (if D.k i = 2 then 16 else 0) +
          (if 3 ≤ D.k i then 34 else 0) + 18 * (D.k i - 3)) := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_ite, Finset.sum_const_zero,
        add_zero, Finset.sum_const, smul_eq_mul]; ring
    have hR : (∑ i ∈ S0, (if S.isU0 i then KerD45Data.resOrdU0 (D.k i) else KerD45Data.resOrdU1 (D.k i))) +
        3 * (S0.filter fun i => D.k i = 1 ∧ S.isU0 i).card +
        5 * (S0.filter fun i => D.k i = 2 ∧ S.isU0 i).card +
        5 * (S0.filter fun i => 3 ≤ D.k i ∧ S.isU0 i).card =
        ∑ i ∈ S0, ((if S.isU0 i then KerD45Data.resOrdU0 (D.k i) else KerD45Data.resOrdU1 (D.k i)) +
          (if D.k i = 1 ∧ S.isU0 i then 3 else 0) + (if D.k i = 2 ∧ S.isU0 i then 5 else 0) +
          (if 3 ≤ D.k i ∧ S.isU0 i then 5 else 0)) := by
      simp only [Finset.sum_add_distrib, Finset.sum_ite, Finset.sum_const_zero,
        add_zero, Finset.sum_const, smul_eq_mul]; ring
    rw [hL, hR]; apply Finset.sum_congr rfl; intro i _; unfold KerD45Data.resOrdU0 KerD45Data.resOrdU1
    by_cases hU : S.isU0 i <;> simp only [hU, and_true, and_false, ↓reduceIte] <;> split_ifs <;> omega
  have heq : 4 * D.n1 + 16 * D.n2 + 34 * D.n3 + 18 * D.nt =
      (∑ i : Idx, (if S.isU0 i then KerD45Data.resOrdU0 (D.k i) else KerD45Data.resOrdU1 (D.k i))) +
      3 * S.n1U + 5 * S.n2U + 5 * S.n3U := by
    unfold n1U n2U n3U KerD45Data.n1 KerD45Data.n2 KerD45Data.n3 KerD45Data.nt
    exact hgen Finset.univ
  have hi := S.U_counts_ineqs
  have := hi.1; have := hi.2.1; have := hi.2.2.1
  omega

end KerD45Syzygy
end B6402Table4Common
end ProximityPrize.SubmissionBinaryLower
