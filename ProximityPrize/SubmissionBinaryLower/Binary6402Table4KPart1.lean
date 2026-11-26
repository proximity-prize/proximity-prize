import ProximityPrize.SubmissionBinaryLower.Binary6402Table4KPart0
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

/-! #### Local orders, domain subset partition, and all `ubCore` / `eqCore` bounds -/

omit K in
lemma isD1_iff (_K : KerD45KData S) (i : Idx) :
    S.D1.eval (BinaryIRSProfile.domain i) = 0 ↔ S.D2.eval (BinaryIRSProfile.domain i ^ 2) = 0 := by
  have h := congrArg (Polynomial.eval (BinaryIRSProfile.domain i)) S.D1_sq
  rw [eval_pow, eval_comp, eval_pow, eval_X] at h
  exact ⟨fun h0 => by rw [← h, h0]; simp, fun h0 => sq_eq_zero_iff.mp (h.trans h0)⟩

omit K in
lemma isU0_of_D1_zero (K : KerD45KData S) {i : Idx} (hD1 : S.D1.eval (BinaryIRSProfile.domain i) = 0) : S.isU0 i :=
  ((S.D2_eval_eq_zero_iff i).mp ((K.isD1_iff i).mp hD1)).2

lemma g2t_zero_of_D1_zero {i : Idx} (hD1 : S.D1.eval (BinaryIRSProfile.domain i) = 0) :
    K.g2t.eval (BinaryIRSProfile.domain i) = 0 := by
  rcases K.hD1_dvd_g2t with ⟨w, hw⟩; rw [hw, eval_mul, hD1, zero_mul]

lemma p1_ne_zero_of_isU0_D1_ne {i : Idx} (hU : S.isU0 i) (hD1 : S.D1.eval (BinaryIRSProfile.domain i) ≠ 0) :
    K.p1.eval (BinaryIRSProfile.domain i ^ 2) ≠ 0 := by
  intro hp10
  have hp0 : S.p.eval (BinaryIRSProfile.domain i ^ 2) = 0 := by
    rw [K.hp_fac, eval_mul, hp10, mul_zero]
  exact hD1 ((K.isD1_iff i).mpr ((S.D2_eval_eq_zero_iff i).mpr ⟨hp0, hU⟩))

lemma q1_ne_zero_of_D1_zero {i : Idx} (hD1 : S.D1.eval (BinaryIRSProfile.domain i) = 0) :
    K.q1.eval (BinaryIRSProfile.domain i ^ 2) ≠ 0 := by
  intro hq10
  have hD20 : S.D2.eval (BinaryIRSProfile.domain i ^ 2) = 0 := (K.isD1_iff i).mp hD1
  have hu := K.hD2_q1_cop.isUnit_of_dvd' (dvd_iff_isRoot.mpr hD20) (dvd_iff_isRoot.mpr hq10)
  have h0 := natDegree_eq_zero_of_isUnit hu; rw [natDegree_X_sub_C] at h0; omega

lemma R1_ne_zero_of_D1_zero {i : Idx} (hD1 : S.D1.eval (BinaryIRSProfile.domain i) = 0) :
    K.R1.eval (BinaryIRSProfile.domain i) ≠ 0 := by
  intro hR10
  apply K.q1_ne_zero_of_D1_zero hD1
  have h := congrArg (Polynomial.eval (BinaryIRSProfile.domain i)) K.hR1_sq
  rw [eval_pow, eval_comp, eval_pow, eval_X, hR10, zero_pow (by norm_num)] at h
  exact h.symm

lemma q1_sh_ne_zero_of_D1_zero {i : Idx} (hD1 : S.D1.eval (BinaryIRSProfile.domain i) = 0) :
    (K.q1 + C (D.y i ^ 2) * S.D2 * K.p1 ^ 2).eval (BinaryIRSProfile.domain i ^ 2) ≠ 0 := by
  have hD20 : S.D2.eval (BinaryIRSProfile.domain i ^ 2) = 0 := (K.isD1_iff i).mp hD1
  simp only [eval_add, eval_mul, eval_C, eval_pow, hD20, mul_zero, zero_mul, add_zero]
  exact K.q1_ne_zero_of_D1_zero hD1

lemma q1_sh_ne_zero_of_not_U0 {i : Idx} (hU : ¬ S.isU0 i) :
    (K.q1 + C (D.y i ^ 2) * S.D2 * K.p1 ^ 2).eval (BinaryIRSProfile.domain i ^ 2) ≠ 0 := by
  intro h0
  set x0 := BinaryIRSProfile.domain i; set t0 := x0 ^ 2; set y0 := D.y i
  have hqsh : (S.q + C (y0 ^ 2) * S.p ^ 2).eval t0 = 0 := by
    have hfac : S.q + C (y0 ^ 2) * S.p ^ 2 = S.D2 * (K.q1 + C (y0 ^ 2) * S.D2 * K.p1 ^ 2) := by
      rw [K.hp_fac, K.hq_fac]; ring
    rw [hfac, eval_mul, h0, mul_zero]
  have hqval : S.q.eval t0 = S.R.eval x0 ^ 2 := by
    have h := congrArg (Polynomial.eval x0) S.q_comp_X_sq
    simpa [eval_comp, eval_pow, eval_X] using h
  have h2 : (2 : Fld) = 0 := CharTwo.two_eq_zero
  have hU2 : S.U_eval i ^ 2 = 0 := by
    unfold KerD45Syzygy.U_eval
    simp only [eval_add, eval_mul, eval_C, eval_pow, hqval] at hqsh
    calc (S.p.eval t0 * y0 + S.R.eval x0) ^ 2
        = S.R.eval x0 ^ 2 + 2 * (S.p.eval t0 * y0) * S.R.eval x0 + y0 ^ 2 * S.p.eval t0 ^ 2 := by ring
      _ = S.R.eval x0 ^ 2 + y0 ^ 2 * S.p.eval t0 ^ 2 := by rw [h2]; ring
      _ = 0 := hqsh
  exact hU (sq_eq_zero_iff.mp hU2)

lemma pow_dvd_K1_all (i : Idx) :
    (X - C (BinaryIRSProfile.domain i ^ 2)) ^ (D.k i - 2) ∣ K.K1 := by
  set x0 := BinaryIRSProfile.domain i; set y0 := D.y i; set t0 := x0 ^ 2
  have hne : (K.P1s + C y0 * K.B1s).eval t0 ≠ 0 ∨ (K.C1s + C x0 * K.B1s).eval t0 ≠ 0 ∨ K.B1s.eval t0 ≠ 0 := by
    by_contra hall; push Not at hall
    have hdB : X - C t0 ∣ K.B1s := dvd_iff_isRoot.mpr hall.2.2
    have hdP : X - C t0 ∣ K.P1s := by
      have h1 : X - C t0 ∣ K.P1s + C y0 * K.B1s := dvd_iff_isRoot.mpr hall.1
      have hrew : K.P1s = (K.P1s + C y0 * K.B1s) + C y0 * K.B1s := by
        rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
      rw [hrew]; exact dvd_add h1 (dvd_mul_of_dvd_right hdB _)
    have hdC : X - C t0 ∣ K.C1s := by
      have h1 : X - C t0 ∣ K.C1s + C x0 * K.B1s := dvd_iff_isRoot.mpr hall.2.1
      have hrew : K.C1s = (K.C1s + C x0 * K.B1s) + C x0 * K.B1s := by
        rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
      rw [hrew]; exact dvd_add h1 (dvd_mul_of_dvd_right hdB _)
    have hu := K.hstar_cop (X - C t0) hdP hdC hdB
    have h0 := natDegree_eq_zero_of_isUnit hu; rw [natDegree_X_sub_C] at h0; omega
  have hloc := D.local_shifted_ords i 1
  have hA0 : D.A0sh y0 1 = K.K1 * (K.P1s + C y0 * K.B1s) := by
    simp only [KerD45Data.A0sh, KerD45Data.Bsh, Fin.val_one]; rw [K.hP1s, K.hB1s]; ring
  have hA1 : D.A1sh x0 y0 1 = K.K1 * (K.C1s + C x0 * K.B1s) := by
    simp only [KerD45Data.A1sh, KerD45Data.Bsh, Fin.val_one]; rw [K.hC1s, K.hB1s]; ring
  have hB : D.Bsh y0 1 = K.K1 * K.B1s := by simp only [KerD45Data.Bsh, Fin.val_one]; exact K.hB1s
  rcases hne with h | h | h
  · have hcop := ((Polynomial.irreducible_X_sub_C t0).coprime_iff_not_dvd.mpr (mt dvd_iff_isRoot.mp h)).pow_left (m := D.k i - 2)
    exact hcop.dvd_of_dvd_mul_right (by rw [← hA0]; exact (pow_dvd_pow _ (by omega)).trans hloc.1)
  · have hcop := ((Polynomial.irreducible_X_sub_C t0).coprime_iff_not_dvd.mpr (mt dvd_iff_isRoot.mp h)).pow_left (m := D.k i - 2)
    exact hcop.dvd_of_dvd_mul_right (by rw [← hA1]; exact (pow_dvd_pow _ (by omega)).trans hloc.2.1)
  · have hcop := ((Polynomial.irreducible_X_sub_C t0).coprime_iff_not_dvd.mpr (mt dvd_iff_isRoot.mp h)).pow_left (m := D.k i - 2)
    exact hcop.dvd_of_dvd_mul_right (by rw [← hB]; exact (pow_dvd_pow _ (by omega : D.k i - 2 ≤ D.k i - 1 - 1)).trans hloc.2.2)

lemma pow_dvd_K1_U1 (i : Idx) (hU : ¬ S.isU0 i) :
    (X - C (BinaryIRSProfile.domain i ^ 2)) ^ (D.k i - 1) ∣ K.K1 := by
  set x0 := BinaryIRSProfile.domain i; set y0 := D.y i; set t0 := x0 ^ 2
  have hne : (K.P1s + C y0 * K.B1s).eval t0 ≠ 0 ∨ (K.C1s + C x0 * K.B1s).eval t0 ≠ 0 ∨ K.B1s.eval t0 ≠ 0 := by
    by_contra hall; push Not at hall
    have hdB : X - C t0 ∣ K.B1s := dvd_iff_isRoot.mpr hall.2.2
    have hdP : X - C t0 ∣ K.P1s := by
      have h1 : X - C t0 ∣ K.P1s + C y0 * K.B1s := dvd_iff_isRoot.mpr hall.1
      have hrew : K.P1s = (K.P1s + C y0 * K.B1s) + C y0 * K.B1s := by rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
      rw [hrew]; exact dvd_add h1 (dvd_mul_of_dvd_right hdB _)
    have hdC : X - C t0 ∣ K.C1s := by
      have h1 : X - C t0 ∣ K.C1s + C x0 * K.B1s := dvd_iff_isRoot.mpr hall.2.1
      have hrew : K.C1s = (K.C1s + C x0 * K.B1s) + C x0 * K.B1s := by rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
      rw [hrew]; exact dvd_add h1 (dvd_mul_of_dvd_right hdB _)
    have hu := K.hstar_cop (X - C t0) hdP hdC hdB
    have h0 := natDegree_eq_zero_of_isUnit hu; rw [natDegree_X_sub_C] at h0; omega
  have hloc := D.local_shifted_ords i 1
  have hB1 := S.pow_dvd_Bsh_U1 i hU 1
  have hA0 : D.A0sh y0 1 = K.K1 * (K.P1s + C y0 * K.B1s) := by
    simp only [KerD45Data.A0sh, KerD45Data.Bsh, Fin.val_one]; rw [K.hP1s, K.hB1s]; ring
  have hA1 : D.A1sh x0 y0 1 = K.K1 * (K.C1s + C x0 * K.B1s) := by
    simp only [KerD45Data.A1sh, KerD45Data.Bsh, Fin.val_one]; rw [K.hC1s, K.hB1s]; ring
  have hB : D.Bsh y0 1 = K.K1 * K.B1s := by simp only [KerD45Data.Bsh, Fin.val_one]; exact K.hB1s
  rcases hne with h | h | h
  · have hcop := ((Polynomial.irreducible_X_sub_C t0).coprime_iff_not_dvd.mpr (mt dvd_iff_isRoot.mp h)).pow_left (m := D.k i - 1)
    exact hcop.dvd_of_dvd_mul_right (by rw [← hA0]; exact hloc.1)
  · have hcop := ((Polynomial.irreducible_X_sub_C t0).coprime_iff_not_dvd.mpr (mt dvd_iff_isRoot.mp h)).pow_left (m := D.k i - 1)
    exact hcop.dvd_of_dvd_mul_right (by rw [← hA1]; exact hloc.2.1)
  · have hcop := ((Polynomial.irreducible_X_sub_C t0).coprime_iff_not_dvd.mpr (mt dvd_iff_isRoot.mp h)).pow_left (m := D.k i - 1)
    exact hcop.dvd_of_dvd_mul_right (by rw [← hB]; exact hB1)

lemma pow_dvd_K1_mbad (i : Idx) (hmb : K.g2t.eval (BinaryIRSProfile.domain i) ≠ 0) :
    (X - C (BinaryIRSProfile.domain i ^ 2)) ^ (D.k i - 1) ∣ K.K1 := by
  set x0 := BinaryIRSProfile.domain i; set y0 := D.y i; set t0 := x0 ^ 2
  have hne : (K.C1s + C x0 * K.B1s).eval t0 ≠ 0 := by
    have hev : (K.C1s + C x0 * K.B1s).eval t0 = K.g2t.eval x0 := by
      rw [K.hg2t_def]; simp [t0]
    rwa [hev]
  have hA1 : D.A1sh x0 y0 1 = K.K1 * (K.C1s + C x0 * K.B1s) := by
    simp only [KerD45Data.A1sh, KerD45Data.Bsh, Fin.val_one]; rw [K.hC1s, K.hB1s]; ring
  have hcop := ((Polynomial.irreducible_X_sub_C t0).coprime_iff_not_dvd.mpr (mt dvd_iff_isRoot.mp hne)).pow_left (m := D.k i - 1)
  exact hcop.dvd_of_dvd_mul_right (by rw [← hA1]; exact (D.local_shifted_ords i 1).2.1)

lemma pow_dvd_Lam1_d2 (i : Idx) (hD1 : S.D1.eval (BinaryIRSProfile.domain i) = 0) :
    (X - C (BinaryIRSProfile.domain i ^ 2)) ^ (D.k i - 1) ∣ K.Lam1 := by
  set x0 := BinaryIRSProfile.domain i; set y0 := D.y i; set t0 := x0 ^ 2
  have hD20 : S.D2.eval t0 = 0 := (K.isD1_iff i).mp hD1
  have hc_ne : S.c.eval t0 ≠ 0 := by
    intro hc0
    have hu := S.D2_coprime_c.isUnit_of_dvd' (dvd_iff_isRoot.mpr hD20) (dvd_iff_isRoot.mpr hc0)
    have h0 := natDegree_eq_zero_of_isUnit hu; rw [natDegree_X_sub_C] at h0; omega
  have hq_ne := K.q1_sh_ne_zero_of_D1_zero hD1
  have hfac_ne : (S.c * (K.q1 + C (y0 ^ 2) * S.D2 * K.p1 ^ 2) ^ 2).eval t0 ≠ 0 := by
    rw [eval_mul, eval_pow]; exact mul_ne_zero hc_ne (pow_ne_zero 2 hq_ne)
  have hcop := ((Polynomial.irreducible_X_sub_C t0).coprime_iff_not_dvd.mpr (mt dvd_iff_isRoot.mp hfac_ne)).pow_left (m := D.k i - 1)
  apply hcop.dvd_of_dvd_mul_left
  rw [K.hLam1_d2_id y0]
  have h0 := D.local_shifted_ords i 0
  exact dvd_add (dvd_mul_of_dvd_left ((pow_dvd_pow _ (by omega)).trans h0.1) K.B1s)
    (dvd_mul_of_dvd_right (by rw [Fin.val_zero, Nat.sub_zero] at h0; exact h0.2.2) _)

lemma pow_dvd_M0s_mbad (i : Idx) (hU : S.isU0 i) (hmb : K.g2t.eval (BinaryIRSProfile.domain i) ≠ 0) :
    (X - C (BinaryIRSProfile.domain i ^ 2)) ^ D.k i ∣ K.M0s := by
  set x0 := BinaryIRSProfile.domain i; set t0 := x0 ^ 2
  have hD1_ne : S.D1.eval x0 ≠ 0 := fun h0 => hmb (K.g2t_zero_of_D1_zero h0)
  have hH1d := S.pow_dvd_H1_of_isU0 i hU
  rw [K.hH1_fac] at hH1d
  have hcop : IsCoprime ((X - C x0) ^ (2 * D.k i - 1)) (S.D1 ^ 4 * K.g2t) := by
    apply IsCoprime.pow_left
    have hne : (S.D1 ^ 4 * K.g2t).eval x0 ≠ 0 := by
      rw [eval_mul, eval_pow]; exact mul_ne_zero (pow_ne_zero 4 hD1_ne) hmb
    exact (Polynomial.irreducible_X_sub_C x0).coprime_iff_not_dvd.mpr (mt dvd_iff_isRoot.mp hne)
  have hMd : (X - C x0) ^ (2 * D.k i - 1) ∣ K.M0s.comp (X ^ 2) :=
    hcop.dvd_of_dvd_mul_left (by rw [show S.D1 ^ 4 * K.g2t * K.M0s.comp (X ^ 2) = S.D1 ^ 4 * K.M0s.comp (X ^ 2) * K.g2t by ring]; exact hH1d)
  have hrm := (le_rootMultiplicity_iff (mt (comp_X_sq_eq_zero_iff K.M0s).mp K.hM0s_ne)).mpr hMd
  have hrm2 : (K.M0s.comp (X ^ 2)).rootMultiplicity x0 = 2 * K.M0s.rootMultiplicity t0 := by
    rw [← rootMultiplicity_map_eq, rootMultiplicity_comp_X_sq_map K.M0s K.hM0s_ne, ← map_pow, rootMultiplicity_map_eq]
  have hle : D.k i ≤ K.M0s.rootMultiplicity t0 := by omega
  exact (pow_dvd_pow _ hle).trans (pow_rootMultiplicity_dvd K.M0s t0)

lemma pow_dvd_Lam1_mul_M0s (i : Idx) [Decidable (S.isU0 i)] :
    (X - C (BinaryIRSProfile.domain i ^ 2)) ^
      (if S.isU0 i then (if D.k i ≤ 1 then 0 else 2 * D.k i - 3)
       else (if D.k i = 0 then 0 else if D.k i = 1 then 1 else 2 * D.k i - 2)) ∣ K.Lam1 * K.M0s := by
  set t0 := BinaryIRSProfile.domain i ^ 2
  have hne : K.Lam1 * K.M0s ≠ 0 := mul_ne_zero K.hLam1_ne K.hM0s_ne
  have hrm_Q2 : S.Q2.rootMultiplicity t0 = 2 * (K.Lam1 * K.M0s).rootMultiplicity t0 := by
    rw [K.hQ2_fac, rootMultiplicity_pow_eq' _ hne 2 t0]
  split_ifs with hU hk1 hk0 hk1'
  · simp
  · have hd := S.pow_dvd_Q2_U0 i; simp only [hk1, ↓reduceIte] at hd
    have hle := (le_rootMultiplicity_iff S.Q2_ne_zero).mpr hd
    rw [hrm_Q2] at hle
    exact (pow_dvd_pow _ (by omega)).trans (pow_rootMultiplicity_dvd _ t0)
  · simp
  · have hd := S.pow_dvd_Q2_U1 i hU; simp only [hk1', Nat.one_ne_zero, ↓reduceIte] at hd
    have hle := (le_rootMultiplicity_iff S.Q2_ne_zero).mpr hd
    rw [hrm_Q2] at hle
    exact (pow_dvd_pow _ (by omega)).trans (pow_rootMultiplicity_dvd _ t0)
  · have hd := S.pow_dvd_Q2_U1 i hU; simp only [hk0, hk1', ↓reduceIte] at hd
    have hle := (le_rootMultiplicity_iff S.Q2_ne_zero).mpr hd
    rw [hrm_Q2] at hle
    exact (pow_dvd_pow _ (by omega)).trans (pow_rootMultiplicity_dvd _ t0)

lemma pow_dvd_g2_din (i : Idx) (hk2 : 2 ≤ D.k i) (hU : S.isU0 i)
    (hg2t : K.g2t.eval (BinaryIRSProfile.domain i) = 0)
    (hM0s : K.M0s.eval (BinaryIRSProfile.domain i ^ 2) = 0)
    (hD1 : S.D1.eval (BinaryIRSProfile.domain i) = 0) :
    (X - C (BinaryIRSProfile.domain i)) ^ 3 ∣ D.gj 2 := by
  set x0 := BinaryIRSProfile.domain i; set y0 := D.y i; set t0 := x0 ^ 2
  set Uy0 := S.p.comp (X ^ 2) * C y0 + S.R
  set U1_y0 := S.D1 * K.p1.comp (X ^ 2) * C y0 + K.R1
  have hU1_ne : U1_y0.eval x0 ≠ 0 := by
    simp only [U1_y0, eval_add, eval_mul, hD1, zero_mul, zero_add]
    exact K.R1_ne_zero_of_D1_zero hD1
  have hU1_pow_ne : (U1_y0 ^ 4).eval x0 ≠ 0 := by rw [eval_pow]; exact pow_ne_zero 4 hU1_ne
  have hcop := ((Polynomial.irreducible_X_sub_C x0).coprime_iff_not_dvd.mpr
    (mt dvd_iff_isRoot.mp hU1_pow_ne)).pow_left (m := 3)
  apply hcop.dvd_of_dvd_mul_right
  rw [← K.h4term_y0 y0]
  have hd_M0s : (X - C x0) ^ 2 ∣ K.M0s.comp (X ^ 2) :=
    (pow_dvd_comp_X_sq_iff K.M0s x0 1).mpr (by rw [pow_one]; exact dvd_iff_isRoot.mpr hM0s)
  have hd_g2t : X - C x0 ∣ K.g2t := dvd_iff_isRoot.mpr hg2t
  have hd_t1 : (X - C x0) ^ 3 ∣ K.M0s.comp (X ^ 2) * K.g2t := by
    rw [show (3 : ℕ) = 2 + 1 by rfl, pow_add, pow_one]; exact mul_dvd_mul hd_M0s hd_g2t
  have hd_D1 : X - C x0 ∣ S.D1 := dvd_iff_isRoot.mpr hD1
  have hd_t2 : (X - C x0) ^ 3 ∣ S.D1 ^ 4 * K.p1.comp (X ^ 2) ^ 4 *
      (D.gj 0 + C (y0 ^ 2) * D.gj 1 + C (y0 ^ 4) * D.gj 2) :=
    dvd_mul_of_dvd_left (dvd_mul_of_dvd_left ((pow_dvd_pow _ (by omega : 3 ≤ 4)).trans (pow_dvd_pow_of_dvd hd_D1 4)) _) _
  have hd_Uy0 : X - C x0 ∣ Uy0 := by
    rw [dvd_iff_isRoot, IsRoot]; simp only [Uy0, eval_add, eval_mul, eval_comp, eval_pow, eval_X, eval_C]; exact hU
  have hd_t3 : (X - C x0) ^ 3 ∣ K.p1.comp (X ^ 2) ^ 2 * Uy0 ^ 2 * D.gj 1 := by
    rw [K.hg1_fac]
    have : (X - C x0) ^ 3 ∣ Uy0 ^ 2 * K.g2t := by
      rw [show (3 : ℕ) = 2 + 1 by rfl, pow_add, pow_one]; exact mul_dvd_mul (pow_dvd_pow_of_dvd hd_Uy0 2) hd_g2t
    exact (this).trans ⟨K.p1.comp (X ^ 2) ^ 2 * K.K1.comp (X ^ 2), by ring⟩
  exact dvd_add (dvd_add hd_t1 hd_t2) hd_t3

omit K in
lemma pow_dvd_g2_U1 (_K : KerD45KData S) (i : Idx) (hU : ¬ S.isU0 i) :
    (X - C (BinaryIRSProfile.domain i)) ^ (2 * (D.k i - 2)) ∣ D.gj 2 := by
  set x0 := BinaryIRSProfile.domain i; set y0 := D.y i; set t0 := x0 ^ 2
  have hrew : D.gj 2 = (D.A1sh x0 y0 2).comp (X ^ 2) + (X - C x0) * (D.Bsh y0 2).comp (X ^ 2) := by
    simp only [KerD45Data.gj, KerD45Data.A1sh, KerD45Data.Bsh, Fin.val_two, add_comp, mul_comp, C_comp,
      sub_eq_add_neg, CharTwo.neg_eq]
    have hz := CharTwo.add_self_eq_zero (C x0 * (D.Bj 2).comp (X ^ 2))
    linear_combination -hz
  rw [hrew]
  apply dvd_add
  · exact (pow_dvd_comp_X_sq_iff _ x0 _).mpr (D.local_shifted_ords i 2).2.1
  · exact dvd_mul_of_dvd_right ((pow_dvd_comp_X_sq_iff _ x0 _).mpr (S.pow_dvd_Bsh_U1 i hU 2)) _

omit K in
lemma pow_dvd_g1_U1 (_K : KerD45KData S) (i : Idx) (hU : ¬ S.isU0 i) :
    (X - C (BinaryIRSProfile.domain i)) ^ (2 * (D.k i - 1)) ∣ D.gj 1 := by
  set x0 := BinaryIRSProfile.domain i; set y0 := D.y i
  have hrew : D.gj 1 = (D.A1sh x0 y0 1).comp (X ^ 2) + (X - C x0) * (D.Bsh y0 1).comp (X ^ 2) := by
    simp only [KerD45Data.gj, KerD45Data.A1sh, KerD45Data.Bsh, Fin.val_one, add_comp, mul_comp, C_comp,
      sub_eq_add_neg, CharTwo.neg_eq]
    have hz := CharTwo.add_self_eq_zero (C x0 * (D.Bj 1).comp (X ^ 2))
    linear_combination -hz
  rw [hrew]
  apply dvd_add
  · exact (pow_dvd_comp_X_sq_iff _ x0 _).mpr (D.local_shifted_ords i 1).2.1
  · exact dvd_mul_of_dvd_right ((pow_dvd_comp_X_sq_iff _ x0 _).mpr (S.pow_dvd_Bsh_U1 i hU 1)) _

omit K in
lemma pow_dvd_g1_U0 (_K : KerD45KData S) (i : Idx) :
    (X - C (BinaryIRSProfile.domain i)) ^ (2 * D.k i - 3) ∣ D.gj 1 := by
  set x0 := BinaryIRSProfile.domain i; set y0 := D.y i
  have hrew : D.gj 1 = (D.A1sh x0 y0 1).comp (X ^ 2) + (X - C x0) * (D.Bsh y0 1).comp (X ^ 2) := by
    simp only [KerD45Data.gj, KerD45Data.A1sh, KerD45Data.Bsh, Fin.val_one, add_comp, mul_comp, C_comp,
      sub_eq_add_neg, CharTwo.neg_eq]
    have hz := CharTwo.add_self_eq_zero (C x0 * (D.Bj 1).comp (X ^ 2))
    linear_combination -hz
  rw [hrew]; have hloc := D.local_shifted_ords i 1
  apply dvd_add
  · exact (pow_dvd_pow _ (by omega : 2 * D.k i - 3 ≤ 2 * (D.k i - 1))).trans ((pow_dvd_comp_X_sq_iff _ x0 _).mpr hloc.2.1)
  · by_cases hk : 2 * D.k i - 3 = 0
    · rw [hk, pow_zero]; exact one_dvd _
    · exact (pow_dvd_pow _ (by omega : 2 * D.k i - 3 ≤ 1 + 2 * (D.k i - 2))).trans
        (by rw [pow_add, pow_one]; exact mul_dvd_mul dvd_rfl ((pow_dvd_comp_X_sq_iff _ x0 _).mpr
          ((pow_dvd_pow _ (by omega : D.k i - 2 ≤ D.k i - 1 - 1)).trans hloc.2.2)))

omit K in
lemma pow_dvd_gsh0 (_K : KerD45KData S) (i : Idx) :
    (X - C (BinaryIRSProfile.domain i)) ^ (2 * D.k i - 1) ∣
      D.gj 0 + C (D.y i ^ 2) * D.gj 1 + C (D.y i ^ 4) * D.gj 2 := by
  set x0 := BinaryIRSProfile.domain i; set y0 := D.y i
  have hrew : D.gj 0 + C (y0 ^ 2) * D.gj 1 + C (y0 ^ 4) * D.gj 2 =
      (D.A1sh x0 y0 0).comp (X ^ 2) + (X - C x0) * (D.Bsh y0 0).comp (X ^ 2) := by
    simp only [KerD45Data.gj, KerD45Data.A1sh, KerD45Data.Bsh, Fin.val_zero, add_comp, mul_comp, C_comp,
      sub_eq_add_neg, CharTwo.neg_eq]
    have hz := CharTwo.add_self_eq_zero (C x0 * ((D.Bj 0).comp (X ^ 2) +
      C (y0 ^ 2) * (D.Bj 1).comp (X ^ 2) + C (y0 ^ 4) * (D.Bj 2).comp (X ^ 2)))
    linear_combination -hz
  rw [hrew]; have hloc := D.local_shifted_ords i 0
  apply dvd_add
  · exact (pow_dvd_pow _ (by omega : 2 * D.k i - 1 ≤ 2 * D.k i)).trans ((pow_dvd_comp_X_sq_iff _ x0 _).mpr (by rw [Fin.val_zero, Nat.sub_zero] at hloc; exact hloc.2.1))
  · by_cases hk : D.k i = 0
    · simp [hk]
    · exact (pow_dvd_pow _ (by omega : 2 * D.k i - 1 ≤ 1 + 2 * (D.k i - 1))).trans
        (by rw [pow_add, pow_one]; exact mul_dvd_mul dvd_rfl ((pow_dvd_comp_X_sq_iff _ x0 _).mpr (by rw [Fin.val_zero, Nat.sub_zero] at hloc; exact hloc.2.2)))

omit K in
lemma pow_dvd_H1_U1 (K : KerD45KData S) (i : Idx) (hU : ¬ S.isU0 i) :
    (X - C (BinaryIRSProfile.domain i)) ^ (2 * (D.k i - 2)) ∣ S.H1 := by
  set x0 := BinaryIRSProfile.domain i; set y0 := D.y i
  set Uy0 := S.p.comp (X ^ 2) * C y0 + S.R
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
    unfold KerD45Syzygy.H1; rw [hR2, hR4]; ring
  rw [hH1_rew]
  exact dvd_add (dvd_add (dvd_mul_of_dvd_right ((pow_dvd_pow _ (by omega : 2 * (D.k i - 2) ≤ 2 * D.k i - 1)).trans (K.pow_dvd_gsh0 i)) _)
    (dvd_mul_of_dvd_right ((pow_dvd_pow _ (by omega : 2 * (D.k i - 2) ≤ 2 * (D.k i - 1))).trans (K.pow_dvd_g1_U1 i hU)) _))
    (dvd_mul_of_dvd_right (K.pow_dvd_g2_U1 i hU) _)

lemma pow_dvd_K_M10sh_d2 (i : Idx) (hD1 : S.D1.eval (BinaryIRSProfile.domain i) = 0) :
    (X - C (BinaryIRSProfile.domain i ^ 2)) ^ (if D.k i ≤ 1 then 0 else 2 * D.k i - 2) ∣ K.K1 * K.Lam1 := by
  set t0 := BinaryIRSProfile.domain i ^ 2; set y0 := D.y i
  have hM10sh : S.M10sh y0 = (K.q1 + C (y0 ^ 2) * S.D2 * K.p1 ^ 2) ^ 2 * (K.K1 * K.Lam1) := by
    unfold KerD45Syzygy.M10sh; rw [K.hM10_fac, K.hM21_fac]
    have h2 : (2 : Fld[X]) = 0 := CharTwo.two_eq_zero
    have hsq : C (y0 ^ 2) ^ 2 = (C (y0 ^ 4) : Fld[X]) := by rw [← map_pow, show (y0 ^ 2) ^ 2 = y0 ^ 4 by ring]
    calc K.q1 ^ 2 * K.K1 * K.Lam1 + C (y0 ^ 4) * (S.D2 ^ 2 * K.p1 ^ 4 * K.K1 * K.Lam1)
        = (K.q1 ^ 2 + 2 * K.q1 * (C (y0 ^ 2) * S.D2 * K.p1 ^ 2) + C (y0 ^ 2) ^ 2 * S.D2 ^ 2 * K.p1 ^ 4) * (K.K1 * K.Lam1) := by
          rw [h2, hsq]; ring
      _ = (K.q1 + C (y0 ^ 2) * S.D2 * K.p1 ^ 2) ^ 2 * (K.K1 * K.Lam1) := by ring
  have hq2_ne : ((K.q1 + C (y0 ^ 2) * S.D2 * K.p1 ^ 2) ^ 2).eval t0 ≠ 0 := by
    rw [eval_pow]; exact pow_ne_zero 2 (K.q1_sh_ne_zero_of_D1_zero hD1)
  have hcop := ((Polynomial.irreducible_X_sub_C t0).coprime_iff_not_dvd.mpr
    (mt dvd_iff_isRoot.mp hq2_ne)).pow_left
      (m := if D.k i ≤ 1 then 0 else 2 * D.k i - 2)
  exact hcop.dvd_of_dvd_mul_left (by rw [← hM10sh]; exact (S.local_shifted_minor_ords i).1.2.2)

lemma pow_dvd_K_U1 (i : Idx) (hU : ¬ S.isU0 i) :
    (X - C (BinaryIRSProfile.domain i ^ 2)) ^ (if D.k i = 0 then 0 else 2 * D.k i - 1) ∣ K.K1 * K.Lam1 := by
  set t0 := BinaryIRSProfile.domain i ^ 2; set y0 := D.y i
  have hM10sh : S.M10sh y0 = (K.q1 + C (y0 ^ 2) * S.D2 * K.p1 ^ 2) ^ 2 * (K.K1 * K.Lam1) := by
    unfold KerD45Syzygy.M10sh; rw [K.hM10_fac, K.hM21_fac]
    have h2 : (2 : Fld[X]) = 0 := CharTwo.two_eq_zero
    have hsq : C (y0 ^ 2) ^ 2 = (C (y0 ^ 4) : Fld[X]) := by rw [← map_pow, show (y0 ^ 2) ^ 2 = y0 ^ 4 by ring]
    calc K.q1 ^ 2 * K.K1 * K.Lam1 + C (y0 ^ 4) * (S.D2 ^ 2 * K.p1 ^ 4 * K.K1 * K.Lam1)
        = (K.q1 ^ 2 + 2 * K.q1 * (C (y0 ^ 2) * S.D2 * K.p1 ^ 2) + C (y0 ^ 2) ^ 2 * S.D2 ^ 2 * K.p1 ^ 4) * (K.K1 * K.Lam1) := by
          rw [h2, hsq]; ring
      _ = (K.q1 + C (y0 ^ 2) * S.D2 * K.p1 ^ 2) ^ 2 * (K.K1 * K.Lam1) := by ring
  have hq2_ne : ((K.q1 + C (y0 ^ 2) * S.D2 * K.p1 ^ 2) ^ 2).eval t0 ≠ 0 := by
    rw [eval_pow]; exact pow_ne_zero 2 (K.q1_sh_ne_zero_of_not_U0 hU)
  have hcop := ((Polynomial.irreducible_X_sub_C t0).coprime_iff_not_dvd.mpr
    (mt dvd_iff_isRoot.mp hq2_ne)).pow_left
      (m := if D.k i = 0 then 0 else 2 * D.k i - 1)
  exact hcop.dvd_of_dvd_mul_left (by rw [← hM10sh]; exact ((S.local_shifted_minor_ords i).2 hU).2.2)

lemma pow_dvd_K_U0_D1_ne (i : Idx) (hU : S.isU0 i) (hD1 : S.D1.eval (BinaryIRSProfile.domain i) ≠ 0) :
    (X - C (BinaryIRSProfile.domain i ^ 2)) ^ (2 * D.k i - 4) ∣ K.K1 * K.Lam1 := by
  set t0 := BinaryIRSProfile.domain i ^ 2
  have hD2_ne : S.D2.eval t0 ≠ 0 := mt (K.isD1_iff i).mpr hD1
  have hp1_ne := K.p1_ne_zero_of_isU0_D1_ne hU hD1
  have hne : (S.D2 ^ 2 * K.p1 ^ 4).eval t0 ≠ 0 := by
    rw [eval_mul, eval_pow, eval_pow]; exact mul_ne_zero (pow_ne_zero 2 hD2_ne) (pow_ne_zero 4 hp1_ne)
  have hcop := ((Polynomial.irreducible_X_sub_C t0).coprime_iff_not_dvd.mpr (mt dvd_iff_isRoot.mp hne)).pow_left
    (m := 2 * D.k i - 4)
  exact hcop.dvd_of_dvd_mul_left (by rw [show S.D2 ^ 2 * K.p1 ^ 4 * (K.K1 * K.Lam1) = S.M21 by rw [K.hM21_fac]; ring]; exact (S.local_shifted_minor_ords i).1.1)

/-! #### Domain subsets and exact counts (`col 0..47`) -/

noncomputable def isMbad (i : Idx) : Prop :=
  2 ≤ D.k i ∧ S.isU0 i ∧ K.g2t.eval (BinaryIRSProfile.domain i) ≠ 0

noncomputable def isML (i : Idx) : Prop :=
  2 ≤ D.k i ∧ S.isU0 i ∧ K.g2t.eval (BinaryIRSProfile.domain i) = 0 ∧
    K.M0s.eval (BinaryIRSProfile.domain i ^ 2) ≠ 0

noncomputable def isNorm (i : Idx) : Prop :=
  2 ≤ D.k i ∧ S.isU0 i ∧ K.g2t.eval (BinaryIRSProfile.domain i) = 0 ∧
    K.M0s.eval (BinaryIRSProfile.domain i ^ 2) = 0

omit K in
noncomputable def isD1 (_K : KerD45KData S) (i : Idx) : Prop := S.D1.eval (BinaryIRSProfile.domain i) = 0

noncomputable def mbadCnt : ℕ := by classical exact (Finset.univ.filter K.isMbad).card
noncomputable def mLCnt : ℕ := by classical exact (Finset.univ.filter K.isML).card
noncomputable def din2Cnt : ℕ := by classical exact (Finset.univ.filter fun i => D.k i = 2 ∧ K.isNorm i ∧ K.isD1 i).card
noncomputable def din3Cnt : ℕ := by classical exact (Finset.univ.filter fun i => 3 ≤ D.k i ∧ K.isNorm i ∧ K.isD1 i).card
noncomputable def dinCnt : ℕ := K.din2Cnt + K.din3Cnt
noncomputable def dmL2Cnt : ℕ := by classical exact (Finset.univ.filter fun i => D.k i = 2 ∧ K.isML i ∧ K.isD1 i).card
noncomputable def dmL3Cnt : ℕ := by classical exact (Finset.univ.filter fun i => 3 ≤ D.k i ∧ K.isML i ∧ K.isD1 i).card
noncomputable def dmLCnt : ℕ := K.dmL2Cnt + K.dmL3Cnt
noncomputable def d2k1UCnt : ℕ := by classical exact (Finset.univ.filter fun i => D.k i = 1 ∧ S.isU0 i ∧ K.isD1 i).card
noncomputable def d2k0Cnt : ℕ := by classical exact (Finset.univ.filter fun i => D.k i = 0 ∧ K.isD1 i).card
noncomputable def mu1Cnt : ℕ := by
  classical exact (Finset.univ.filter fun i => D.k i = 1 ∧ S.isU0 i ∧ ¬ K.isD1 i ∧
    K.M0s.eval (BinaryIRSProfile.domain i ^ 2) = 0).card
noncomputable def ntUNorm : ℕ := by classical exact ∑ i : Idx, if K.isNorm i then D.k i - 3 else 0
noncomputable def ntUMbad : ℕ := by classical exact ∑ i : Idx, if K.isMbad i then D.k i - 3 else 0
noncomputable def ntUML : ℕ := by classical exact ∑ i : Idx, if K.isML i then D.k i - 3 else 0
noncomputable def muExK3 : ℕ := by
  classical exact ∑ i : Idx,
    if 3 ≤ D.k i ∧ K.isNorm i then K.M0s.rootMultiplicity (BinaryIRSProfile.domain i ^ 2) - 1
    else if 3 ≤ D.k i ∧ K.isMbad i then K.M0s.rootMultiplicity (BinaryIRSProfile.domain i ^ 2) - 2
    else 0

lemma card_filter_univ_Z {P : Idx → Prop} (inst1 inst2 : DecidablePred P) :
    ((@Finset.filter Idx P inst1 Finset.univ).card : ℤ) =
      ∑ i : Idx, @ite ℤ (P i) (inst2 i) 1 0 := by
  have hgen : ∀ S0 : Finset Idx,
      ((@Finset.filter Idx P inst1 S0).card : ℤ) = ∑ i ∈ S0, @ite ℤ (P i) (inst2 i) 1 0 := by
    intro S0
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, mul_one]
    congr 1; apply congrArg Finset.card; ext i
    simp only [Finset.mem_filter]
  exact hgen Finset.univ

lemma sum_ite_nat_Z {P : Idx → Prop} (g : Idx → ℕ) (inst1 inst2 : DecidablePred P) :
    ((∑ i : Idx, @ite ℕ (P i) (inst1 i) (g i) 0 : ℕ) : ℤ) =
      ∑ i : Idx, @ite ℤ (P i) (inst2 i) ((g i : ℕ) : ℤ) 0 := by
  rw [Nat.cast_sum]
  apply Finset.sum_congr rfl; intro i _
  by_cases h : P i <;> simp [h]

lemma n0_Z [DecidablePred fun i : Idx => D.k i = 0] :
    (D.n0 : ℤ) = ∑ i : Idx, (if D.k i = 0 then (1 : ℤ) else 0) := by
  unfold KerD45Data.n0; exact card_filter_univ_Z _ _
lemma n1_Z [DecidablePred fun i : Idx => D.k i = 1] :
    (D.n1 : ℤ) = ∑ i : Idx, (if D.k i = 1 then (1 : ℤ) else 0) := by
  unfold KerD45Data.n1; exact card_filter_univ_Z _ _
lemma n2_Z [DecidablePred fun i : Idx => D.k i = 2] :
    (D.n2 : ℤ) = ∑ i : Idx, (if D.k i = 2 then (1 : ℤ) else 0) := by
  unfold KerD45Data.n2; exact card_filter_univ_Z _ _
lemma n3_Z [DecidablePred fun i : Idx => 3 ≤ D.k i] :
    (D.n3 : ℤ) = ∑ i : Idx, (if 3 ≤ D.k i then (1 : ℤ) else 0) := by
  unfold KerD45Data.n3; exact card_filter_univ_Z _ _
lemma nt_Z : (D.nt : ℤ) = ∑ i : Idx, ((D.k i - 3 : ℕ) : ℤ) := by
  unfold KerD45Data.nt; rw [Nat.cast_sum]
lemma n1U_Z [DecidablePred fun i : Idx => D.k i = 1 ∧ S.isU0 i] :
    (S.n1U : ℤ) = ∑ i : Idx, (if D.k i = 1 ∧ S.isU0 i then (1 : ℤ) else 0) := by
  unfold KerD45Syzygy.n1U; exact card_filter_univ_Z _ _
lemma n2U_Z [DecidablePred fun i : Idx => D.k i = 2 ∧ S.isU0 i] :
    (S.n2U : ℤ) = ∑ i : Idx, (if D.k i = 2 ∧ S.isU0 i then (1 : ℤ) else 0) := by
  unfold KerD45Syzygy.n2U; exact card_filter_univ_Z _ _
lemma n3U_Z [DecidablePred fun i : Idx => 3 ≤ D.k i ∧ S.isU0 i] :
    (S.n3U : ℤ) = ∑ i : Idx, (if 3 ≤ D.k i ∧ S.isU0 i then (1 : ℤ) else 0) := by
  unfold KerD45Syzygy.n3U; exact card_filter_univ_Z _ _
lemma mbadCnt_Z [DecidablePred K.isMbad] :
    (K.mbadCnt : ℤ) = ∑ i : Idx, (if K.isMbad i then (1 : ℤ) else 0) := by
  unfold mbadCnt; exact card_filter_univ_Z _ _
lemma mLCnt_Z [DecidablePred K.isML] :
    (K.mLCnt : ℤ) = ∑ i : Idx, (if K.isML i then (1 : ℤ) else 0) := by
  unfold mLCnt; exact card_filter_univ_Z _ _
lemma din2Cnt_Z [DecidablePred fun i : Idx => D.k i = 2 ∧ K.isNorm i ∧ K.isD1 i] :
    (K.din2Cnt : ℤ) = ∑ i : Idx, (if D.k i = 2 ∧ K.isNorm i ∧ K.isD1 i then (1 : ℤ) else 0) := by
  unfold din2Cnt; exact card_filter_univ_Z _ _
lemma din3Cnt_Z [DecidablePred fun i : Idx => 3 ≤ D.k i ∧ K.isNorm i ∧ K.isD1 i] :
    (K.din3Cnt : ℤ) = ∑ i : Idx, (if 3 ≤ D.k i ∧ K.isNorm i ∧ K.isD1 i then (1 : ℤ) else 0) := by
  unfold din3Cnt; exact card_filter_univ_Z _ _
lemma dmL2Cnt_Z [DecidablePred fun i : Idx => D.k i = 2 ∧ K.isML i ∧ K.isD1 i] :
    (K.dmL2Cnt : ℤ) = ∑ i : Idx, (if D.k i = 2 ∧ K.isML i ∧ K.isD1 i then (1 : ℤ) else 0) := by
  unfold dmL2Cnt; exact card_filter_univ_Z _ _
lemma dmL3Cnt_Z [DecidablePred fun i : Idx => 3 ≤ D.k i ∧ K.isML i ∧ K.isD1 i] :
    (K.dmL3Cnt : ℤ) = ∑ i : Idx, (if 3 ≤ D.k i ∧ K.isML i ∧ K.isD1 i then (1 : ℤ) else 0) := by
  unfold dmL3Cnt; exact card_filter_univ_Z _ _
lemma d2k1UCnt_Z [DecidablePred fun i : Idx => D.k i = 1 ∧ S.isU0 i ∧ K.isD1 i] :
    (K.d2k1UCnt : ℤ) = ∑ i : Idx, (if D.k i = 1 ∧ S.isU0 i ∧ K.isD1 i then (1 : ℤ) else 0) := by
  unfold d2k1UCnt; exact card_filter_univ_Z _ _
lemma d2k0Cnt_Z [DecidablePred fun i : Idx => D.k i = 0 ∧ K.isD1 i] :
    (K.d2k0Cnt : ℤ) = ∑ i : Idx, (if D.k i = 0 ∧ K.isD1 i then (1 : ℤ) else 0) := by
  unfold d2k0Cnt; exact card_filter_univ_Z _ _
lemma mu1Cnt_Z [DecidablePred fun i : Idx => D.k i = 1 ∧ S.isU0 i ∧ ¬ K.isD1 i ∧ K.M0s.eval (BinaryIRSProfile.domain i ^ 2) = 0] :
    (K.mu1Cnt : ℤ) = ∑ i : Idx, (if D.k i = 1 ∧ S.isU0 i ∧ ¬ K.isD1 i ∧ K.M0s.eval (BinaryIRSProfile.domain i ^ 2) = 0 then (1 : ℤ) else 0) := by
  unfold mu1Cnt; exact card_filter_univ_Z _ _
lemma ntUNorm_Z [DecidablePred K.isNorm] :
    (K.ntUNorm : ℤ) = ∑ i : Idx, (if K.isNorm i then ((D.k i - 3 : ℕ) : ℤ) else 0) := by
  unfold ntUNorm; exact sum_ite_nat_Z (fun i => D.k i - 3) _ _
lemma ntUMbad_Z [DecidablePred K.isMbad] :
    (K.ntUMbad : ℤ) = ∑ i : Idx, (if K.isMbad i then ((D.k i - 3 : ℕ) : ℤ) else 0) := by
  unfold ntUMbad; exact sum_ite_nat_Z (fun i => D.k i - 3) _ _
lemma ntUML_Z [DecidablePred K.isML] :
    (K.ntUML : ℤ) = ∑ i : Idx, (if K.isML i then ((D.k i - 3 : ℕ) : ℤ) else 0) := by
  unfold ntUML; exact sum_ite_nat_Z (fun i => D.k i - 3) _ _
lemma muExK3_Z [DecidablePred fun i : Idx => 3 ≤ D.k i ∧ K.isNorm i] [DecidablePred fun i : Idx => 3 ≤ D.k i ∧ K.isMbad i] :
    (K.muExK3 : ℤ) = ∑ i : Idx, ((if 3 ≤ D.k i ∧ K.isNorm i then K.M0s.rootMultiplicity (BinaryIRSProfile.domain i ^ 2) - 1
      else if 3 ≤ D.k i ∧ K.isMbad i then K.M0s.rootMultiplicity (BinaryIRSProfile.domain i ^ 2) - 2 else 0 : ℕ) : ℤ) := by
  unfold muExK3; rw [Nat.cast_sum]
  apply Finset.sum_congr rfl; intro i _
  by_cases h1 : 3 ≤ D.k i ∧ K.isNorm i <;> by_cases h2 : 3 ≤ D.k i ∧ K.isMbad i <;> simp [h1, h2]

lemma ntU_split : K.ntUNorm + K.ntUMbad + K.ntUML = S.ntU := by
  classical
  unfold ntUNorm ntUMbad ntUML KerD45Syzygy.ntU
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro i _
  unfold isNorm isMbad isML
  by_cases hU : S.isU0 i
  · by_cases hk3 : 3 ≤ D.k i
    · have hk2 : 2 ≤ D.k i := by omega
      by_cases hg : K.g2t.eval (BinaryIRSProfile.domain i) = 0
      · by_cases hm : K.M0s.eval (BinaryIRSProfile.domain i ^ 2) = 0
        · simp [hU, hk2, hg, hm]
        · simp [hU, hk2, hg, hm]
      · simp [hU, hk2, hg]
    · have h0 : D.k i - 3 = 0 := by omega
      simp [h0]
  · simp [hU]

lemma K1_base_le : (D.n2 - S.n2U) + (2 * D.n3 - S.n3U) + D.nt + K.mbadCnt ≤ K.K1.natDegree := by
  classical
  let f : Idx → ℕ := fun i =>
    if D.k i ≤ 1 then 0 else if S.isU0 i then (if K.isMbad i then D.k i - 1 else D.k i - 2) else D.k i - 1
  have hdvd : ∀ i ∈ (Finset.univ : Finset Idx), (X - C (BinaryIRSProfile.domain i ^ 2)) ^ f i ∣ K.K1 := fun i _ => by
    dsimp [f]; split_ifs with hk hU hmb
    · simp
    · exact K.pow_dvd_K1_mbad i hmb.2.2
    · exact K.pow_dvd_K1_all i
    · exact K.pow_dvd_K1_U1 i hU
  have hle := sum_ord_le_natDegree_of_dvd Finset.univ (fun i => BinaryIRSProfile.domain i ^ 2)
    domain_sq_injective K.K1 K.hK1_ne f hdvd
  have hU := S.U_counts_ineqs
  have hZ : ((D.n2 - S.n2U) + (2 * D.n3 - S.n3U) + D.nt + K.mbadCnt : ℤ) = ∑ i : Idx, (f i : ℤ) := by
    have hrew : ((D.n2 : ℤ) - (S.n2U : ℤ)) + (2 * (D.n3 : ℤ) - (S.n3U : ℤ)) + (D.nt : ℤ) + (K.mbadCnt : ℤ) =
        ∑ i : Idx, ((if D.k i = 2 then (1 : ℤ) else 0) - (if D.k i = 2 ∧ S.isU0 i then 1 else 0) +
          2 * (if 3 ≤ D.k i then 1 else 0) - (if 3 ≤ D.k i ∧ S.isU0 i then 1 else 0) +
          ((D.k i - 3 : ℕ) : ℤ) + (if K.isMbad i then 1 else 0)) := by
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
        ← n0_Z, ← n1_Z, ← n2_Z, ← n3_Z, ← nt_Z, ← n1U_Z, ← n2U_Z, ← n3U_Z,
        ← K.mbadCnt_Z, ← K.mLCnt_Z, ← K.din2Cnt_Z, ← K.din3Cnt_Z, ← K.dmL2Cnt_Z, ← K.dmL3Cnt_Z,
        ← K.d2k1UCnt_Z, ← K.d2k0Cnt_Z, ← K.mu1Cnt_Z, ← K.ntUNorm_Z, ← K.ntUMbad_Z, ← K.ntUML_Z, ← K.muExK3_Z] <;> ring
    rw [show ((D.n2 - S.n2U) + (2 * D.n3 - S.n3U) + D.nt + K.mbadCnt : ℤ) =
        ((D.n2 : ℤ) - (S.n2U : ℤ)) + (2 * (D.n3 : ℤ) - (S.n3U : ℤ)) + (D.nt : ℤ) + (K.mbadCnt : ℤ) by omega, hrew]
    apply Finset.sum_congr rfl; intro i _
    dsimp [f]
    by_cases hU : S.isU0 i <;> by_cases hg : K.g2t.eval (BinaryIRSProfile.domain i) = 0 <;>
      simp only [isMbad, hU, hg, ne_eq, not_true_eq_false, not_false_eq_true, and_true, and_false, true_and, false_and, ↓reduceIte] <;>
      (try split_ifs) <;> omega
  rw [← Nat.cast_sum] at hZ; omega

lemma M0s_base_le :
    (S.n2U + S.n3U + K.mbadCnt - K.mLCnt) + K.mu1Cnt + K.muExK3 ≤ K.M0s.natDegree := by
  classical
  let f : Idx → ℕ := fun i =>
    if K.isNorm i then (if 3 ≤ D.k i then K.M0s.rootMultiplicity (BinaryIRSProfile.domain i ^ 2) else 1)
    else if K.isMbad i then (if 3 ≤ D.k i then K.M0s.rootMultiplicity (BinaryIRSProfile.domain i ^ 2) else 2)
    else if D.k i = 1 ∧ S.isU0 i ∧ ¬ K.isD1 i ∧ K.M0s.eval (BinaryIRSProfile.domain i ^ 2) = 0 then 1
    else 0
  have hdvd : ∀ i ∈ (Finset.univ : Finset Idx), (X - C (BinaryIRSProfile.domain i ^ 2)) ^ f i ∣ K.M0s := fun i _ => by
    dsimp [f]; split_ifs with hn hk3 hmb hk3' hmu1
    · exact pow_rootMultiplicity_dvd K.M0s _
    · rw [pow_one]; exact dvd_iff_isRoot.mpr hn.2.2.2
    · exact pow_rootMultiplicity_dvd K.M0s _
    · exact (pow_dvd_pow _ hmb.1).trans (K.pow_dvd_M0s_mbad i hmb.2.1 hmb.2.2)
    · rw [pow_one]; exact dvd_iff_isRoot.mpr hmu1.2.2.2
    · simp
  have hle := sum_ord_le_natDegree_of_dvd Finset.univ (fun i => BinaryIRSProfile.domain i ^ 2)
    domain_sq_injective K.M0s K.hM0s_ne f hdvd
  have hmb_mL : K.mbadCnt + K.mLCnt ≤ S.n2U + S.n3U := by
    have hZ : (K.mbadCnt : ℤ) + (K.mLCnt : ℤ) ≤ (S.n2U : ℤ) + (S.n3U : ℤ) := by
      have h1 : (K.mbadCnt : ℤ) + (K.mLCnt : ℤ) = ∑ i : Idx, ((if K.isMbad i then (1 : ℤ) else 0) + (if K.isML i then 1 else 0)) := by
        rw [Finset.sum_add_distrib, ← K.mbadCnt_Z, ← K.mLCnt_Z]
      have h2 : (S.n2U : ℤ) + (S.n3U : ℤ) = ∑ i : Idx, ((if D.k i = 2 ∧ S.isU0 i then (1 : ℤ) else 0) + (if 3 ≤ D.k i ∧ S.isU0 i then 1 else 0)) := by
        rw [Finset.sum_add_distrib, ← n2U_Z, ← n3U_Z]
      rw [h1, h2]; apply Finset.sum_le_sum; intro i _
      by_cases hU : S.isU0 i <;> by_cases hg : K.g2t.eval (BinaryIRSProfile.domain i) = 0 <;>
        by_cases hm : K.M0s.eval (BinaryIRSProfile.domain i ^ 2) = 0 <;>
        simp only [isMbad, isML, hU, hg, hm, ne_eq, not_true_eq_false, not_false_eq_true, and_true, and_false, true_and, false_and, ↓reduceIte] <;>
        (try split_ifs) <;> omega
    omega
  have hZ : ((S.n2U + S.n3U + K.mbadCnt - K.mLCnt) + K.mu1Cnt + K.muExK3 : ℤ) = ∑ i : Idx, (f i : ℤ) := by
    have hrew : ((S.n2U : ℤ) + (S.n3U : ℤ) + (K.mbadCnt : ℤ) - (K.mLCnt : ℤ)) + (K.mu1Cnt : ℤ) + (K.muExK3 : ℤ) =
        ∑ i : Idx, ((if D.k i = 2 ∧ S.isU0 i then (1 : ℤ) else 0) + (if 3 ≤ D.k i ∧ S.isU0 i then 1 else 0) +
          (if K.isMbad i then 1 else 0) - (if K.isML i then 1 else 0) +
          (if D.k i = 1 ∧ S.isU0 i ∧ ¬ K.isD1 i ∧ K.M0s.eval (BinaryIRSProfile.domain i ^ 2) = 0 then 1 else 0) +
          ((if 3 ≤ D.k i ∧ K.isNorm i then K.M0s.rootMultiplicity (BinaryIRSProfile.domain i ^ 2) - 1
            else if 3 ≤ D.k i ∧ K.isMbad i then K.M0s.rootMultiplicity (BinaryIRSProfile.domain i ^ 2) - 2 else 0 : ℕ) : ℤ)) := by
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
        ← n0_Z, ← n1_Z, ← n2_Z, ← n3_Z, ← nt_Z, ← n1U_Z, ← n2U_Z, ← n3U_Z,
        ← K.mbadCnt_Z, ← K.mLCnt_Z, ← K.din2Cnt_Z, ← K.din3Cnt_Z, ← K.dmL2Cnt_Z, ← K.dmL3Cnt_Z,
        ← K.d2k1UCnt_Z, ← K.d2k0Cnt_Z, ← K.mu1Cnt_Z, ← K.ntUNorm_Z, ← K.ntUMbad_Z, ← K.ntUML_Z, ← K.muExK3_Z]
    rw [show ((S.n2U + S.n3U + K.mbadCnt - K.mLCnt) + K.mu1Cnt + K.muExK3 : ℤ) =
        ((S.n2U : ℤ) + (S.n3U : ℤ) + (K.mbadCnt : ℤ) - (K.mLCnt : ℤ)) + (K.mu1Cnt : ℤ) + (K.muExK3 : ℤ) by omega, hrew]
    apply Finset.sum_congr rfl; intro i _
    dsimp [f]
    by_cases hn : K.isNorm i
    · have hrm1 : 1 ≤ K.M0s.rootMultiplicity (BinaryIRSProfile.domain i ^ 2) :=
        (le_rootMultiplicity_iff K.hM0s_ne).mpr (by rw [pow_one]; exact dvd_iff_isRoot.mpr hn.2.2.2)
      have hU := hn.2.1; have hg := hn.2.2.1; have hm := hn.2.2.2; have hk2 := hn.1
      simp only [hn, isNorm, isMbad, isML, hU, hg, hm, ne_eq, not_true_eq_false, not_false_eq_true, and_true, and_false, true_and, false_and, ↓reduceIte]
      (try split_ifs) <;> omega
    · by_cases hmb : K.isMbad i
      · have hrm2 : 2 ≤ K.M0s.rootMultiplicity (BinaryIRSProfile.domain i ^ 2) :=
          (le_rootMultiplicity_iff K.hM0s_ne).mpr ((pow_dvd_pow _ hmb.1).trans (K.pow_dvd_M0s_mbad i hmb.2.1 hmb.2.2))
        have hU := hmb.2.1; have hg : ¬ (K.g2t.eval (BinaryIRSProfile.domain i) = 0) := hmb.2.2; have hk2 := hmb.1
        simp only [hn, hmb, isNorm, isMbad, isML, hU, hg, ne_eq, not_true_eq_false, not_false_eq_true, and_true, and_false, true_and, false_and, ↓reduceIte]
        (try split_ifs) <;> omega
      · by_cases hU : S.isU0 i <;> by_cases hD1 : K.isD1 i <;>
          by_cases hg : K.g2t.eval (BinaryIRSProfile.domain i) = 0 <;>
          by_cases hm : K.M0s.eval (BinaryIRSProfile.domain i ^ 2) = 0 <;>
          simp only [isNorm, isMbad, isML, hU, hD1, hg, hm, ne_eq, not_true_eq_false, not_false_eq_true,
            and_true, and_false, true_and, false_and, ↓reduceIte] at hn hmb ⊢ <;>
          (try split_ifs) <;> omega
  rw [← Nat.cast_sum] at hZ; omega

end KerD45KData
end B6402Table4K
end ProximityPrize.SubmissionBinaryLower
