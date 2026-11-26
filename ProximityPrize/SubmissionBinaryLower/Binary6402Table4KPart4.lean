import ProximityPrize.SubmissionBinaryLower.Binary6402Table4KPart3
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

noncomputable def g2rem : Fld[X] := Classical.choose K.Sg2_dvd_g2t
noncomputable def Hrem : Fld[X] := Classical.choose K.N1_Shit3_cube_dvd_Hraw
noncomputable def Qpoly : Fld[X] := K.M0 ^ 3 * K.N1 ^ 2 * D.gj 2

lemma g2t_eq_Sg2_mul_g2rem : K.g2t = K.Sg2 * K.g2rem := Classical.choose_spec K.Sg2_dvd_g2t
lemma Hraw_eq_N1_Shit3_Hrem : K.M0s.comp (X ^ 2) * K.g2t = K.N1 * K.Shit3 ^ 3 * K.Hrem :=
  Classical.choose_spec K.N1_Shit3_cube_dvd_Hraw

lemma g2rem_ne : K.g2rem ≠ 0 := by intro h0; apply K.hg2t_ne; rw [K.g2t_eq_Sg2_mul_g2rem, h0, mul_zero]
lemma Hrem_ne : K.Hrem ≠ 0 := by
  intro h0
  have h1 := K.Hraw_eq_N1_Shit3_Hrem; rw [h0, mul_zero] at h1
  exact mul_ne_zero (mt (comp_X_sq_eq_zero_iff K.M0s).mp K.hM0s_ne) K.hg2t_ne h1
lemma Qpoly_ne : K.Qpoly ≠ 0 :=
  mul_ne_zero (mul_ne_zero (pow_ne_zero 3 K.M0_ne) (pow_ne_zero 2 K.N1_ne)) D.g2_ne_zero

lemma natDegree_g2rem : K.g2rem.natDegree = K.g2t.natDegree - (S.n2U + S.n3U - K.mbadCnt) := by
  have h := congrArg Polynomial.natDegree K.g2t_eq_Sg2_mul_g2rem
  rw [natDegree_mul K.Sg2_ne K.g2rem_ne] at h
  unfold Sg2 at h; rw [linProd_natDegree, K.card_I_g2] at h; omega

lemma natDegree_Hrem :
    K.Hrem.natDegree = 2 * K.M0s.natDegree + K.g2t.natDegree - (S.n1U + K.dmLCnt) - 3 * (S.n2U + S.n3U - K.dmLCnt) := by
  have h := congrArg Polynomial.natDegree K.Hraw_eq_N1_Shit3_Hrem
  rw [natDegree_mul (mt (comp_X_sq_eq_zero_iff K.M0s).mp K.hM0s_ne) K.hg2t_ne, natDegree_comp_X_sq,
    natDegree_mul (mul_ne_zero K.N1_ne (pow_ne_zero 3 K.Shit3_ne)) K.Hrem_ne,
    natDegree_mul K.N1_ne (pow_ne_zero 3 K.Shit3_ne), natDegree_pow] at h
  unfold N1 Shit3 at h; rw [linProd_natDegree, linProd_natDegree, K.card_I_N1, K.card_I_hit3] at h
  omega

/-- Exact squarefree decomposition `M0eff * D.gj 2 * g2rem = S_K^2 * H_K` with `Squarefree H_K`! -/
noncomputable def sfK :=
  exists_sq_mul_squarefree (K.M0eff * D.gj 2 * K.g2rem)
    (mul_ne_zero (mul_ne_zero K.M0eff_ne D.g2_ne_zero) K.g2rem_ne)

noncomputable def SK : Fld[X] := Classical.choose K.sfK
noncomputable def HK : Fld[X] := Classical.choose (Classical.choose_spec K.sfK)

lemma HK_decomp : K.M0eff * D.gj 2 * K.g2rem = K.SK ^ 2 * K.HK := (Classical.choose_spec (Classical.choose_spec K.sfK)).1
lemma HK_sqfree : Squarefree K.HK := (Classical.choose_spec (Classical.choose_spec K.sfK)).2
lemma SK_ne : K.SK ≠ 0 := by
  intro h0; apply mul_ne_zero (mul_ne_zero K.M0eff_ne D.g2_ne_zero) K.g2rem_ne
  rw [K.HK_decomp, h0, zero_pow (by norm_num), zero_mul]
lemma HK_ne : K.HK ≠ 0 := K.HK_sqfree.ne_zero

/-- Exact Wronskian identity for `H_K`:
`SK^2 * (C c0 * HK + Ndom * HK') = M0eff^2 * D1^6 * p1(X^2)^5 * Lam1(X^2)`! -/
theorem HK_wronskian {c0 : Fld} (hd1 : Ndom.derivative = C c0) :
    K.SK ^ 2 * (C c0 * K.HK + Ndom * K.HK.derivative) =
      K.M0eff ^ 2 * S.D1 ^ 6 * K.p1.comp (X ^ 2) ^ 5 * K.Lam1.comp (X ^ 2) := by
  have h1 : Ndom * (K.g2t * D.gj 2) = K.Sg2 ^ 2 * K.SK ^ 2 * K.HK := by
    calc Ndom * (K.g2t * D.gj 2) = (K.M0eff * K.Sg2) * (K.Sg2 * K.g2rem * D.gj 2) := by
          rw [← K.Ndom_eq_M0eff_Sg2, ← K.g2t_eq_Sg2_mul_g2rem]
      _ = K.Sg2 ^ 2 * (K.M0eff * D.gj 2 * K.g2rem) := by ring
      _ = K.Sg2 ^ 2 * K.SK ^ 2 * K.HK := by rw [K.HK_decomp]; ring
  have hdiff := congrArg Polynomial.derivative h1
  rw [derivative_mul, hd1, K.hwr_g2t_g2,
    show K.Sg2 ^ 2 * K.SK ^ 2 * K.HK = (K.Sg2 * K.SK) ^ 2 * K.HK by ring,
    derivative_mul, char2_derivative_sq, zero_mul, zero_add] at hdiff
  have hm := congrArg (· * Ndom) hdiff
  have h2 : C c0 * (K.g2t * D.gj 2) * Ndom = K.Sg2 ^ 2 * K.SK ^ 2 * (C c0 * K.HK) := by
    calc C c0 * (K.g2t * D.gj 2) * Ndom = C c0 * (Ndom * (K.g2t * D.gj 2)) := by ring
      _ = K.Sg2 ^ 2 * K.SK ^ 2 * (C c0 * K.HK) := by rw [h1]; ring
  have h3 : Ndom * (S.D1 ^ 6 * K.p1.comp (X ^ 2) ^ 5 * K.Lam1.comp (X ^ 2)) * Ndom =
      K.Sg2 ^ 2 * (K.M0eff ^ 2 * S.D1 ^ 6 * K.p1.comp (X ^ 2) ^ 5 * K.Lam1.comp (X ^ 2)) := by
    rw [K.Ndom_eq_M0eff_Sg2]; ring
  apply mul_left_cancel₀ (pow_ne_zero 2 K.Sg2_ne)
  have hz := CharTwo.add_self_eq_zero (K.Sg2 ^ 2 * K.SK ^ 2 * (C c0 * K.HK))
  rw [add_mul, h2, h3] at hm
  linear_combination -hm + hz

/-- Exact bridge `Shit3^4 * (Hrem * Qpoly) = (M0 * sqrtPoly M0s)^2 * Ndom * (g2t * D.gj 2)`
and its Wronskian consequence! -/
theorem Hrem_Q_bridge :
    K.Shit3 ^ 4 * (K.Hrem * K.Qpoly) = (K.M0 * sqrtPoly K.M0s) ^ 2 * Ndom * (K.g2t * D.gj 2) := by
  apply mul_left_cancel₀ K.N1_ne
  have hsq : (sqrtPoly K.M0s) ^ 2 = K.M0s.comp (X ^ 2) := sqrtPoly_sq K.M0s
  calc K.N1 * (K.Shit3 ^ 4 * (K.Hrem * K.Qpoly))
      = (K.N1 * K.Shit3 ^ 3 * K.Hrem) * (K.M0 ^ 3 * K.N1 ^ 2 * K.Shit3 * D.gj 2) := by unfold Qpoly; ring
    _ = (K.M0s.comp (X ^ 2) * K.g2t) * (K.M0 ^ 3 * K.N1 ^ 2 * K.Shit3 * D.gj 2) := by rw [← K.Hraw_eq_N1_Shit3_Hrem]
    _ = K.N1 * ((K.M0 * sqrtPoly K.M0s) ^ 2 * (K.M0 * K.N1 * K.Shit3) * (K.g2t * D.gj 2)) := by rw [← hsq]; ring
    _ = K.N1 * ((K.M0 * sqrtPoly K.M0s) ^ 2 * Ndom * (K.g2t * D.gj 2)) := by rw [← K.Ndom_eq_M0_N1_Shit3]

theorem Hrem_Q_wronskian {c0 : Fld} (hd1 : Ndom.derivative = C c0) :
    K.Shit3 ^ 4 * (Ndom * (K.Hrem.derivative * K.Qpoly + K.Hrem * K.Qpoly.derivative) + C c0 * K.Hrem * K.Qpoly) =
      (K.M0 * sqrtPoly K.M0s * Ndom) ^ 2 * S.D1 ^ 6 * K.p1.comp (X ^ 2) ^ 5 * K.Lam1.comp (X ^ 2) := by
  have h1 := K.Hrem_Q_bridge
  have hdiff := congrArg Polynomial.derivative h1
  rw [derivative_mul, char2_derivative_pow_four, zero_mul, zero_add, derivative_mul,
    mul_assoc ((K.M0 * sqrtPoly K.M0s) ^ 2), derivative_mul, char2_derivative_sq, zero_mul, zero_add,
    derivative_mul, hd1, K.hwr_g2t_g2] at hdiff
  have hm := congrArg (· * Ndom) hdiff
  have h2 : (K.M0 * sqrtPoly K.M0s) ^ 2 * (C c0 * (K.g2t * D.gj 2)) * Ndom =
      K.Shit3 ^ 4 * (C c0 * K.Hrem * K.Qpoly) := by
    calc (K.M0 * sqrtPoly K.M0s) ^ 2 * (C c0 * (K.g2t * D.gj 2)) * Ndom
        = C c0 * ((K.M0 * sqrtPoly K.M0s) ^ 2 * Ndom * (K.g2t * D.gj 2)) := by ring
      _ = C c0 * (K.Shit3 ^ 4 * (K.Hrem * K.Qpoly)) := by rw [← h1]
      _ = K.Shit3 ^ 4 * (C c0 * K.Hrem * K.Qpoly) := by ring
  have hz := CharTwo.add_self_eq_zero (K.Shit3 ^ 4 * (C c0 * K.Hrem * K.Qpoly))
  simp only [mul_add, add_mul] at hm
  rw [h2] at hm
  linear_combination hm + hz

/-- Exact `ODE_fail` 4-term identity for `(Hrem, Qpoly)` at ANY `y0 : Fld`! -/
theorem Hrem_Q_ode_fail_id (y0 : Fld) :
    let Uy0 := S.p.comp (X ^ 2) * C y0 + S.R
    let U1_y0 := S.D1 * K.p1.comp (X ^ 2) * C y0 + K.R1
    let R_raw := S.D1 ^ 4 * K.p1.comp (X ^ 2) ^ 2 * (D.gj 0 + C (y0 ^ 2) * D.gj 1 + C (y0 ^ 4) * D.gj 2) +
      Uy0 ^ 2 * D.gj 1
    K.Hrem * Ndom ^ 3 + (sqrtPoly K.p1) ^ 4 * (K.M0 ^ 3 * K.N1 ^ 2 * R_raw) = K.Qpoly * U1_y0 ^ 4 := by
  intro Uy0 U1_y0 R_raw
  have hp4 : (sqrtPoly K.p1) ^ 4 = K.p1.comp (X ^ 2) ^ 2 := by
    calc (sqrtPoly K.p1) ^ 4 = ((sqrtPoly K.p1) ^ 2) ^ 2 := by ring
      _ = K.p1.comp (X ^ 2) ^ 2 := by rw [sqrtPoly_sq]
  have h1 := congrArg (· * (K.M0 ^ 3 * K.N1 ^ 2)) (K.h4term_y0 y0)
  have ht1 : K.M0s.comp (X ^ 2) * K.g2t * (K.M0 ^ 3 * K.N1 ^ 2) = K.Hrem * Ndom ^ 3 := by
    rw [K.Hraw_eq_N1_Shit3_Hrem, K.Ndom_eq_M0_N1_Shit3]; ring
  rw [add_mul, add_mul, ht1] at h1
  rw [hp4]; unfold Qpoly; dsimp [R_raw]
  linear_combination h1

end KerD45KData

/-! ### Part 3: Pointwise 15-Column `Step15Pt` Bridge, `B1_0C`, `ODE_holds`, and `ODE_fail` -/

namespace KerD45KData

variable {D : KerD45Data} {S : KerD45Syzygy D} (K : KerD45KData S)

/-- Classify any `a ∈ AlgebraicClosure Fld` into its exact `Step15Pt` type! -/
noncomputable def ptOf (a : AlgebraicClosure Fld) : Step15Pt := by
  classical
  let ι : Fld →+* AlgebraicClosure Fld := algebraMap Fld (AlgebraicClosure Fld)
  exact if h : ∃ i : Idx, a = ι (BinaryIRSProfile.domain i) then
    let i := Classical.choose h
    if D.k i = 0 then .k0
    else if D.k i = 1 then if S.isU0 i then .k1U else .k0
    else if ¬ S.isU0 i then .k2noU
    else if D.k i = 2 then
      if K.isNorm i then .k2U else if K.isML i then .k2U_mL else .k2U_mb
    else
      if K.isNorm i then .k3U else if K.isML i then .k3U_mL else .k3U_mb
  else .out

open Classical in
lemma ptOf_dom (i : Idx) :
    K.ptOf (algebraMap Fld (AlgebraicClosure Fld) (BinaryIRSProfile.domain i)) =
      if D.k i = 0 then .k0
      else if D.k i = 1 then if S.isU0 i then .k1U else .k0
      else if ¬ S.isU0 i then .k2noU
      else if D.k i = 2 then
        if K.isNorm i then .k2U else if K.isML i then .k2U_mL else .k2U_mb
      else
        if K.isNorm i then .k3U else if K.isML i then .k3U_mL else .k3U_mb := by
  let ι : Fld →+* AlgebraicClosure Fld := algebraMap Fld (AlgebraicClosure Fld)
  unfold ptOf
  have hex : ∃ j : Idx, ι (BinaryIRSProfile.domain i) = ι (BinaryIRSProfile.domain j) := ⟨i, rfl⟩
  rw [dif_pos hex]
  have hch : Classical.choose hex = i :=
    BinaryIRSProfile.domain.injective (ι.injective (Classical.choose_spec hex).symm)
  rw [hch]

lemma ptOf_out {a : AlgebraicClosure Fld}
    (h : ¬ ∃ i : Idx, a = algebraMap Fld (AlgebraicClosure Fld) (BinaryIRSProfile.domain i)) :
    K.ptOf a = .out := by
  classical unfold ptOf; rw [dif_neg h]

lemma ptOf_dom_spec (i : Idx) :
    let pt := K.ptOf (algebraMap Fld (AlgebraicClosure Fld) (BinaryIRSProfile.domain i))
    (pt = .k1U → D.k i = 1 ∧ S.isU0 i) ∧
    (pt = .k2noU → 2 ≤ D.k i ∧ ¬ S.isU0 i) ∧
    (pt = .k2U → D.k i = 2 ∧ K.isNorm i) ∧
    (pt = .k2U_mL → D.k i = 2 ∧ K.isML i) ∧
    (pt = .k2U_mb → D.k i = 2 ∧ K.isMbad i) ∧
    (pt = .k3U → 3 ≤ D.k i ∧ K.isNorm i) ∧
    (pt = .k3U_mL → 3 ≤ D.k i ∧ K.isML i) ∧
    (pt = .k3U_mb → 3 ≤ D.k i ∧ K.isMbad i) := by
  classical
  dsimp only; rw [K.ptOf_dom i]
  by_cases hk0 : D.k i = 0
  · simp [hk0]
  · by_cases hk1 : D.k i = 1
    · by_cases hU : S.isU0 i <;> simp [hk0, hk1, hU]
    · by_cases hU : S.isU0 i
      · by_cases hk2 : D.k i = 2
        · by_cases hn : K.isNorm i
          · simp [hk0, hk1, hU, hk2, hn]
          · by_cases hmL : K.isML i
            · simp [hk0, hk1, hU, hk2, hn, hmL]
            · have hmb : K.isMbad i := by
                refine ⟨by omega, hU, ?_⟩
                intro hg; by_cases hm : K.M0s.eval (BinaryIRSProfile.domain i ^ 2) = 0
                · exact hn ⟨by omega, hU, hg, hm⟩
                · exact hmL ⟨by omega, hU, hg, hm⟩
              simp [hk0, hk1, hU, hk2, hn, hmL, hmb]
        · have hk3 : 3 ≤ D.k i := by omega
          by_cases hn : K.isNorm i
          · simp [hk0, hk1, hU, hk2, hk3, hn]
          · by_cases hmL : K.isML i
            · simp [hk0, hk1, hU, hk2, hk3, hn, hmL]
            · have hmb : K.isMbad i := by
                refine ⟨by omega, hU, ?_⟩
                intro hg; by_cases hm : K.M0s.eval (BinaryIRSProfile.domain i ^ 2) = 0
                · exact hn ⟨by omega, hU, hg, hm⟩
                · exact hmL ⟨by omega, hU, hg, hm⟩
              simp [hk0, hk1, hU, hk2, hk3, hn, hmL, hmb]
      · have hk2 : 2 ≤ D.k i := by omega
        simp [hk0, hk1, hU, hk2]

-- Local 15-column parameter tuple at `a ∈ AlgebraicClosure Fld`.
omit K in
noncomputable def L0_l (_K : KerD45KData S) (a : AlgebraicClosure Fld) : ℕ := by
  classical
  exact if h : ∃ i : Idx, a = algebraMap Fld (AlgebraicClosure Fld) (BinaryIRSProfile.domain i) then
    let i := Classical.choose h
    if 3 ≤ D.k i ∧ S.isU0 i then 2 * (D.k i - 3) else 0
  else 0

omit K in
noncomputable def LnoU_l (_K : KerD45KData S) (a : AlgebraicClosure Fld) : ℕ := by
  classical
  exact if h : ∃ i : Idx, a = algebraMap Fld (AlgebraicClosure Fld) (BinaryIRSProfile.domain i) then
    let i := Classical.choose h
    if 3 ≤ D.k i ∧ ¬ S.isU0 i then 2 * (D.k i - 3) else 0
  else 0

noncomputable def a1_l (a : AlgebraicClosure Fld) : ℕ :=
  (K.p1.map (algebraMap Fld (AlgebraicClosure Fld))).rootMultiplicity (a ^ 2)

omit K in
noncomputable def d2_l (_K : KerD45KData S) (a : AlgebraicClosure Fld) : ℕ :=
  (S.D1.map (algebraMap Fld (AlgebraicClosure Fld))).rootMultiplicity a

noncomputable def muRaw_l (a : AlgebraicClosure Fld) : ℕ :=
  (K.M0s.map (algebraMap Fld (AlgebraicClosure Fld))).rootMultiplicity (a ^ 2)

noncomputable def muEx_l (a : AlgebraicClosure Fld) : ℕ :=
  K.muRaw_l a - muSub (K.ptOf a)

noncomputable def lam_l (a : AlgebraicClosure Fld) : ℕ :=
  (K.Lam1.map (algebraMap Fld (AlgebraicClosure Fld))).rootMultiplicity (a ^ 2)

noncomputable def g_l (a : AlgebraicClosure Fld) : ℕ :=
  (K.SK.map (algebraMap Fld (AlgebraicClosure Fld))).rootMultiplicity a

noncomputable def b_l (a : AlgebraicClosure Fld) : ℕ :=
  (K.HK.map (algebraMap Fld (AlgebraicClosure Fld))).rootMultiplicity a

noncomputable def e1_l (a : AlgebraicClosure Fld) : ℕ :=
  (K.g2rem.map (algebraMap Fld (AlgebraicClosure Fld))).rootMultiplicity a

omit K in
noncomputable def c_l (_K : KerD45KData S) (a : AlgebraicClosure Fld) : ℕ :=
  ((D.gj 2).map (algebraMap Fld (AlgebraicClosure Fld))).rootMultiplicity a

lemma M0eff_rm_eq_mVal (a : AlgebraicClosure Fld) :
    ((K.M0eff.map (algebraMap Fld (AlgebraicClosure Fld))).rootMultiplicity a) = (K.ptOf a).mVal := by
  classical
  let ι : Fld →+* AlgebraicClosure Fld := algebraMap Fld (AlgebraicClosure Fld)
  unfold M0eff; rw [linProd_rm]
  by_cases h : ∃ i : Idx, a = ι (BinaryIRSProfile.domain i)
  · rcases h with ⟨i, rfl⟩
    rw [K.ptOf_dom i]
    have hmem : (∃ j ∈ K.I_M0eff, ι (BinaryIRSProfile.domain i) = ι (BinaryIRSProfile.domain j)) ↔ i ∈ K.I_M0eff := by
      constructor
      · rintro ⟨j, hj, heq⟩; have := BinaryIRSProfile.domain.injective (ι.injective heq); rwa [this]
      · intro hi; exact ⟨i, hi, rfl⟩
    rw [if_congr hmem rfl rfl]
    have hmem2 : i ∈ K.I_M0eff ↔ D.k i ≤ 1 ∨ ¬ S.isU0 i ∨ K.isMbad i := by
      unfold I_M0eff; rw [Finset.mem_filter]; simp only [Finset.mem_univ, true_and]
    rw [if_congr hmem2 rfl rfl]
    by_cases hU : S.isU0 i <;> by_cases hg : K.g2t.eval (BinaryIRSProfile.domain i) = 0 <;>
      by_cases hm : K.M0s.eval (BinaryIRSProfile.domain i ^ 2) = 0 <;>
      simp only [isNorm, isML, isMbad, hU, hg, hm, ne_eq, not_true_eq_false, not_false_eq_true,
        and_true, and_false, true_and, false_and, or_true, or_false, ↓reduceIte] <;>
      (try split_ifs) <;> simp [Step15Pt.mVal, Step15Pt.m0, Step15Pt.mbad, Step15Pt.m1, Step15Pt.m2] <;> omega
  · rw [K.ptOf_out h, if_neg (fun h' => by rcases h' with ⟨i, _, hi⟩; exact h ⟨i, hi⟩)]
    rfl

lemma Sg2_rm_eq (a : AlgebraicClosure Fld) :
    ((K.Sg2.map (algebraMap Fld (AlgebraicClosure Fld))).rootMultiplicity a) = (K.ptOf a).nu - (K.ptOf a).mVal := by
  classical
  let ι : Fld →+* AlgebraicClosure Fld := algebraMap Fld (AlgebraicClosure Fld)
  unfold Sg2; rw [linProd_rm]
  by_cases h : ∃ i : Idx, a = ι (BinaryIRSProfile.domain i)
  · rcases h with ⟨i, rfl⟩
    rw [K.ptOf_dom i]
    have hmem : (∃ j ∈ K.I_g2, ι (BinaryIRSProfile.domain i) = ι (BinaryIRSProfile.domain j)) ↔ i ∈ K.I_g2 := by
      constructor
      · rintro ⟨j, hj, heq⟩; have := BinaryIRSProfile.domain.injective (ι.injective heq); rwa [this]
      · intro hi; exact ⟨i, hi, rfl⟩
    rw [if_congr hmem rfl rfl]
    have hmem2 : i ∈ K.I_g2 ↔ 2 ≤ D.k i ∧ S.isU0 i ∧ ¬ K.isMbad i := by
      unfold I_g2; rw [Finset.mem_filter]; simp only [Finset.mem_univ, true_and]
    rw [if_congr hmem2 rfl rfl]
    by_cases hU : S.isU0 i <;> by_cases hg : K.g2t.eval (BinaryIRSProfile.domain i) = 0 <;>
      by_cases hm : K.M0s.eval (BinaryIRSProfile.domain i ^ 2) = 0 <;>
      simp only [isNorm, isML, isMbad, hU, hg, hm, ne_eq, not_true_eq_false, not_false_eq_true,
        and_true, and_false, true_and, false_and, ↓reduceIte] <;>
      (try split_ifs) <;> simp [Step15Pt.nu, Step15Pt.mVal, Step15Pt.m0, Step15Pt.mbad, Step15Pt.m1, Step15Pt.m2] <;> omega
  · rw [K.ptOf_out h, if_neg (fun h' => by rcases h' with ⟨i, _, hi⟩; exact h ⟨i, hi⟩)]; rfl

lemma d2_l_le_one (a : AlgebraicClosure Fld) : K.d2_l a ≤ 1 := by
  unfold d2_l KerD45Syzygy.D1
  rw [rootMultiplicity_sqrtPoly_map S.D2 S.D2_ne_zero a]
  exact rootMultiplicity_map_le_one_of_squarefree S.D2_squarefree (a ^ 2)

lemma v_Q_sub_Hrem (a : AlgebraicClosure Fld) :
    ((K.Qpoly.map (algebraMap Fld (AlgebraicClosure Fld))).rootMultiplicity a : ℤ) -
    ((K.Hrem.map (algebraMap Fld (AlgebraicClosure Fld))).rootMultiplicity a : ℤ) =
      (K.c_l a : ℤ) - (K.e1_l a : ℤ) + 2 * ((K.ptOf a).nu : ℤ) + ((K.ptOf a).mVal : ℤ) -
        2 * (K.muRaw_l a : ℤ) := by
  let E := AlgebraicClosure Fld
  let ι : Fld →+* E := algebraMap Fld E
  have hQ_rm : (K.Qpoly.map ι).rootMultiplicity a =
      3 * (K.M0.map ι).rootMultiplicity a + 2 * (K.N1.map ι).rootMultiplicity a + K.c_l a := by
    have hM0E := (Polynomial.map_ne_zero_iff ι.injective).mpr K.M0_ne
    have hN1E := (Polynomial.map_ne_zero_iff ι.injective).mpr K.N1_ne
    have hg2E := (Polynomial.map_ne_zero_iff ι.injective).mpr D.g2_ne_zero
    unfold Qpoly c_l
    rw [Polynomial.map_mul, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_pow,
      rootMultiplicity_mul (mul_ne_zero (mul_ne_zero (pow_ne_zero 3 hM0E) (pow_ne_zero 2 hN1E)) hg2E),
      rootMultiplicity_mul (mul_ne_zero (pow_ne_zero 3 hM0E) (pow_ne_zero 2 hN1E)),
      rootMultiplicity_pow_eq' _ hM0E 3 a, rootMultiplicity_pow_eq' _ hN1E 2 a]
  have hH_rm : (K.N1.map ι).rootMultiplicity a + 3 * (K.Shit3.map ι).rootMultiplicity a +
      (K.Hrem.map ι).rootMultiplicity a = 2 * K.muRaw_l a + ((K.ptOf a).nu - (K.ptOf a).mVal) + K.e1_l a := by
    have hN1E := (Polynomial.map_ne_zero_iff ι.injective).mpr K.N1_ne
    have hS3E := (Polynomial.map_ne_zero_iff ι.injective).mpr K.Shit3_ne
    have hHrE := (Polynomial.map_ne_zero_iff ι.injective).mpr K.Hrem_ne
    have hMcE := (Polynomial.map_ne_zero_iff ι.injective).mpr (mt (comp_X_sq_eq_zero_iff K.M0s).mp K.hM0s_ne)
    have hg2tE := (Polynomial.map_ne_zero_iff ι.injective).mpr K.hg2t_ne
    have hSg2E := (Polynomial.map_ne_zero_iff ι.injective).mpr K.Sg2_ne
    have hg2rE := (Polynomial.map_ne_zero_iff ι.injective).mpr K.g2rem_ne
    have h1 := congrArg (fun f : Fld[X] => (f.map ι).rootMultiplicity a) K.Hraw_eq_N1_Shit3_Hrem
    simp only [Polynomial.map_mul, Polynomial.map_pow] at h1
    rw [rootMultiplicity_mul (mul_ne_zero hMcE hg2tE),
      rootMultiplicity_mul (mul_ne_zero (mul_ne_zero hN1E (pow_ne_zero 3 hS3E)) hHrE),
      rootMultiplicity_mul (mul_ne_zero hN1E (pow_ne_zero 3 hS3E)),
      rootMultiplicity_pow_eq' _ hS3E 3 a,
      rootMultiplicity_comp_X_sq_map K.M0s K.hM0s_ne a] at h1
    have h2 := congrArg (fun f : Fld[X] => (f.map ι).rootMultiplicity a) K.g2t_eq_Sg2_mul_g2rem
    rw [Polynomial.map_mul, rootMultiplicity_mul (mul_ne_zero hSg2E hg2rE), K.Sg2_rm_eq a] at h2
    have hι : ι = algebraMap Fld (AlgebraicClosure Fld) := rfl
    rw [h2] at h1; rw [hι] at h1 ⊢; unfold muRaw_l e1_l; omega
  have hNdom_rm : (K.M0.map ι).rootMultiplicity a + (K.N1.map ι).rootMultiplicity a +
      (K.Shit3.map ι).rootMultiplicity a = (K.ptOf a).nu := by
    have hM0E := (Polynomial.map_ne_zero_iff ι.injective).mpr K.M0_ne
    have hN1E := (Polynomial.map_ne_zero_iff ι.injective).mpr K.N1_ne
    have hS3E := (Polynomial.map_ne_zero_iff ι.injective).mpr K.Shit3_ne
    have h1 := congrArg (fun f : Fld[X] => (f.map ι).rootMultiplicity a) K.Ndom_eq_M0_N1_Shit3
    simp only [Polynomial.map_mul] at h1
    rw [rootMultiplicity_mul (mul_ne_zero (mul_ne_zero hM0E hN1E) hS3E),
      rootMultiplicity_mul (mul_ne_zero hM0E hN1E)] at h1
    have hN_eq : (Ndom.map ι).rootMultiplicity a = (K.ptOf a).nu := by
      unfold Ndom; rw [show (∏ i : Idx, (X - C (BinaryIRSProfile.domain i))) = linProd Finset.univ from rfl, linProd_rm]
      by_cases h : ∃ i : Idx, a = ι (BinaryIRSProfile.domain i)
      · rcases h with ⟨i, rfl⟩
        rw [if_pos ⟨i, Finset.mem_univ i, rfl⟩, K.ptOf_dom i]
        split_ifs <;> rfl
      · rw [if_neg (fun h' => by rcases h' with ⟨i, _, hi⟩; exact h ⟨i, hi⟩), K.ptOf_out h]; rfl
    omega
  have hm_le_nu : (K.ptOf a).mVal ≤ (K.ptOf a).nu := by cases K.ptOf a <;> decide
  have hι : ι = algebraMap Fld (AlgebraicClosure Fld) := rfl
  rw [hι] at hQ_rm hH_rm hNdom_rm
  omega

/-- Master local-hypothesis bundle at `a ∈ AlgebraicClosure Fld` for all 15-col STEP theorems! -/
lemma local_step15_core (a : AlgebraicClosure Fld) :
    let pt := K.ptOf a
    let L0 := K.L0_l a
    let LnoU := K.LnoU_l a
    let a1 := K.a1_l a
    let d2 := K.d2_l a
    let mu := K.muEx_l a
    let lam := K.lam_l a
    let g := K.g_l a
    let b := K.b_l a
    let e1 := K.e1_l a
    let c := K.c_l a
    d2 ≤ 1 ∧ b ≤ 1 ∧ L0 % 2 = 0 ∧ LnoU % 2 = 0 ∧
    (0 < L0 → pt = .k3U ∨ pt = .k3U_mL ∨ pt = .k3U_mb) ∧
    (0 < LnoU → pt = .k2noU) ∧
    ((pt = .k2noU ∨ pt = .k2U_mb ∨ pt = .k3U_mb) → d2 = 0) ∧
    ((pt = .k2U ∨ pt = .k2U_mL ∨ pt = .k2U_mb ∨ pt = .k3U ∨ pt = .k3U_mL ∨ pt = .k3U_mb ∨ pt = .k1U) → d2 = 0 → a1 = 0) ∧
    ((pt = .k2U_mL ∨ pt = .k3U_mL) → mu = 0) ∧
    (pt = .k2noU → (LnoU = 0 → 2 ≤ lam + mu) ∧ (0 < LnoU → 4 + LnoU ≤ lam + mu)) ∧
    (pt = .k2U_mL → 1 ≤ lam) ∧
    (pt = .k3U → 2 + L0 ≤ lam + mu) ∧
    (pt = .k3U_mL → 3 + L0 ≤ lam) ∧
    (pt = .k3U_mb → 1 + L0 / 2 ≤ mu) ∧
    (pt = .k1U → (d2 = 1 ∨ mu = 0) → 1 ≤ e1) ∧
    ((pt = .k2U_mL ∨ pt = .k3U_mL) → d2 = 0 → 2 ≤ e1) ∧
    (g ≤ pt.mVal + lam + 3 * d2 + 5 * a1) ∧
    (c + e1 + pt.mVal = 2 * g + b) ∧
    (pt.mbad = 0 → pt.vChat mu e1 c =
      ((K.Qpoly.map (algebraMap Fld (AlgebraicClosure Fld))).rootMultiplicity a : ℤ) -
      ((K.Hrem.map (algebraMap Fld (AlgebraicClosure Fld))).rootMultiplicity a : ℤ)) ∧
    (pt.mbad = 1 → (c : ℤ) - (e1 : ℤ) - 1 - 2 * (mu : ℤ) =
      ((K.Qpoly.map (algebraMap Fld (AlgebraicClosure Fld))).rootMultiplicity a : ℤ) -
      ((K.Hrem.map (algebraMap Fld (AlgebraicClosure Fld))).rootMultiplicity a : ℤ)) ∧
    (1 ≤ a1 ∨ 1 ≤ d2 ∨ pt = .k2noU →
      let t1 := 8 * a1 + 4 * d2 + 3 * pt.mVal + pt.vc0 d2 e1 c L0 LnoU
      let t2 := 4 * a1 + 2 * d2 + 2 * pt.k1Min d2 lam L0 LnoU + (pt.nu - pt.mVal) + 3 * pt.mVal + e1
      let t3 := pt.t3 d2 mu e1
      let t4 := c + 3 * pt.mVal
      (t4 > t3 → min t1 t2 ≤ t3) ∧ (t4 < t3 → min t1 t2 ≤ t4)) := by
  classical
  let E := AlgebraicClosure Fld
  let ι : Fld →+* E := algebraMap Fld E
  obtain ⟨c0, c1, L, hc0, _, _, _, _, hd1, _, _, _⟩ := Ndom_decomp
  intro pt L0 LnoU a1 d2 mu lam g b e1 c
  have hd2_le : d2 ≤ 1 := K.d2_l_le_one a
  have hb_le : b ≤ 1 := rootMultiplicity_map_le_one_of_squarefree K.HK_sqfree a
  have hL0_ev : L0 % 2 = 0 := by dsimp [L0, L0_l]; split_ifs <;> omega
  have hLnoU_ev : LnoU % 2 = 0 := by dsimp [LnoU, LnoU_l]; split_ifs <;> omega
  -- Helper to extract i whenever pt ≠ .out!
  have hdom_of_pt : pt ≠ .out → ∃ i : Idx, a = ι (BinaryIRSProfile.domain i) := fun hne => by
    by_contra h; exact hne (K.ptOf_out h)
  -- Helper: evaluate rootMultiplicity at domain i!
  have hrm_dom_D1 : ∀ i : Idx, a = ι (BinaryIRSProfile.domain i) → (d2 = 0 ↔ ¬ K.isD1 i) := fun i hi => by
    dsimp [d2, d2_l]; rw [hi, rootMultiplicity_map_eq, rootMultiplicity_eq_zero_iff]
    exact ⟨fun h hr => S.D1_ne_zero (h hr), fun h hr => absurd hr h⟩
  have hrm_dom_p1 : ∀ i : Idx, a = ι (BinaryIRSProfile.domain i) → (a1 = 0 ↔ K.p1.eval (BinaryIRSProfile.domain i ^ 2) ≠ 0) := fun i hi => by
    dsimp [a1, a1_l]; rw [hi, ← map_pow, rootMultiplicity_map_eq, rootMultiplicity_eq_zero_iff]
    exact ⟨fun h hr => K.hp1_ne (h hr), fun h hr => absurd hr h⟩
  have hrm_dom_M0s : ∀ i : Idx, a = ι (BinaryIRSProfile.domain i) → K.muRaw_l a = K.M0s.rootMultiplicity (BinaryIRSProfile.domain i ^ 2) := fun i hi => by
    dsimp [muRaw_l]; rw [hi, ← map_pow, rootMultiplicity_map_eq]
  have hrm_dom_Lam1 : ∀ i : Idx, a = ι (BinaryIRSProfile.domain i) → lam = K.Lam1.rootMultiplicity (BinaryIRSProfile.domain i ^ 2) := fun i hi => by
    dsimp [lam, lam_l]; rw [hi, ← map_pow, rootMultiplicity_map_eq]
  have hrm_dom_g2t : ∀ i : Idx, a = ι (BinaryIRSProfile.domain i) →
      K.g2t.rootMultiplicity (BinaryIRSProfile.domain i) = (pt.nu - pt.mVal) + e1 := fun i hi => by
    have hι : ι = algebraMap Fld (AlgebraicClosure Fld) := rfl
    have h1 := congrArg (fun f : Fld[X] => (f.map ι).rootMultiplicity a) K.g2t_eq_Sg2_mul_g2rem
    rw [Polynomial.map_mul, rootMultiplicity_mul (mul_ne_zero ((Polynomial.map_ne_zero_iff ι.injective).mpr K.Sg2_ne)
      ((Polynomial.map_ne_zero_iff ι.injective).mpr K.g2rem_ne)), K.Sg2_rm_eq a] at h1
    have hL : (K.g2t.map ι).rootMultiplicity a = K.g2t.rootMultiplicity (BinaryIRSProfile.domain i) := by
      rw [hi, rootMultiplicity_map_eq]
    rw [hL, hι] at h1; exact h1
  -- Exact muRaw_l lower bounds for k2U/k3U/k2U_mb/k3U_mb!
  have hmuRaw_ge1 : (pt = .k2U ∨ pt = .k3U) → 1 ≤ K.muRaw_l a := fun hpt => by
    obtain ⟨i, hi⟩ := hdom_of_pt (by rcases hpt with h | h <;> simp [h])
    rw [hrm_dom_M0s i hi]
    have hsp := K.ptOf_dom_spec i
    have hn : K.isNorm i := by
      dsimp [pt] at hpt; rw [hi] at hpt
      rcases hpt with h | h
      · exact (hsp.2.2.1 h).2
      · exact (hsp.2.2.2.2.2.1 h).2
    exact (le_rootMultiplicity_iff K.hM0s_ne).mpr (by rw [pow_one]; exact dvd_iff_isRoot.mpr hn.2.2.2)
  have hmuRaw_mb : (pt = .k2U_mb ∨ pt = .k3U_mb) →
      2 ≤ K.muRaw_l a ∧ (pt = .k3U_mb → 3 + L0 / 2 ≤ K.muRaw_l a) := fun hpt => by
    obtain ⟨i, hi⟩ := hdom_of_pt (by rcases hpt with h | h <;> simp [h])
    rw [hrm_dom_M0s i hi]
    have hsp := K.ptOf_dom_spec i
    have hL0_i : L0 = if 3 ≤ D.k i ∧ S.isU0 i then 2 * (D.k i - 3) else 0 := by
      dsimp [L0, L0_l]; rw [dif_pos ⟨i, hi⟩]
      have hch : Classical.choose (⟨i, hi⟩ : ∃ j, a = ι (BinaryIRSProfile.domain j)) = i :=
        BinaryIRSProfile.domain.injective (ι.injective ((Classical.choose_spec (⟨i, hi⟩ : ∃ j, a = ι (BinaryIRSProfile.domain j))).symm.trans hi))
      rw [hch]
    have hmb : K.isMbad i := by
      dsimp [pt] at hpt; rw [hi] at hpt
      rcases hpt with h | h
      · exact (hsp.2.2.2.2.1 h).2
      · exact (hsp.2.2.2.2.2.2.2 h).2
    have hd := K.pow_dvd_M0s_mbad i hmb.2.1 hmb.2.2
    have hle := (le_rootMultiplicity_iff K.hM0s_ne).mpr hd
    refine ⟨by have := hmb.1; omega, fun h3 => ?_⟩
    have hk3 : 3 ≤ D.k i := by dsimp [pt] at h3; rw [hi] at h3; exact (hsp.2.2.2.2.2.2.2 h3).1
    rw [if_pos ⟨hk3, hmb.2.1⟩] at hL0_i; omega
  -- hS and htot from HK_wronskian & HK_decomp!
  have hS_bound : g ≤ pt.mVal + lam + 3 * d2 + 5 * a1 := by
    have hwr := congrArg (Polynomial.map ι) (K.HK_wronskian hd1)
    simp only [Polynomial.map_mul, Polynomial.map_pow] at hwr
    have hRHS_ne : (K.M0eff.map ι) ^ 2 * (S.D1.map ι) ^ 6 * ((K.p1.comp (X ^ 2)).map ι) ^ 5 *
        ((K.Lam1.comp (X ^ 2)).map ι) ≠ 0 :=
      mul_ne_zero (mul_ne_zero (mul_ne_zero
        (pow_ne_zero 2 ((Polynomial.map_ne_zero_iff ι.injective).mpr K.M0eff_ne))
        (pow_ne_zero 6 ((Polynomial.map_ne_zero_iff ι.injective).mpr S.D1_ne_zero)))
        (pow_ne_zero 5 ((Polynomial.map_ne_zero_iff ι.injective).mpr (mt (comp_X_sq_eq_zero_iff _).mp K.hp1_ne))))
        ((Polynomial.map_ne_zero_iff ι.injective).mpr (mt (comp_X_sq_eq_zero_iff _).mp K.hLam1_ne))
    have hdvd : (K.SK.map ι) ^ 2 ∣ (K.M0eff.map ι) ^ 2 * (S.D1.map ι) ^ 6 *
        ((K.p1.comp (X ^ 2)).map ι) ^ 5 * ((K.Lam1.comp (X ^ 2)).map ι) :=
      ⟨(C c0 * K.HK + Ndom * K.HK.derivative).map ι, hwr.symm⟩
    have hle := Polynomial.rootMultiplicity_le_rootMultiplicity_of_dvd hRHS_ne hdvd a
    have hSKE := (Polynomial.map_ne_zero_iff ι.injective).mpr K.SK_ne
    have hME := (Polynomial.map_ne_zero_iff ι.injective).mpr K.M0eff_ne
    have hD1E := (Polynomial.map_ne_zero_iff ι.injective).mpr S.D1_ne_zero
    have hp1E := (Polynomial.map_ne_zero_iff ι.injective).mpr (mt (comp_X_sq_eq_zero_iff _).mp K.hp1_ne)
    have hLE := (Polynomial.map_ne_zero_iff ι.injective).mpr (mt (comp_X_sq_eq_zero_iff _).mp K.hLam1_ne)
    rw [rootMultiplicity_pow_eq' _ hSKE 2 a,
      rootMultiplicity_mul hRHS_ne,
      rootMultiplicity_mul (mul_ne_zero (mul_ne_zero (pow_ne_zero 2 hME) (pow_ne_zero 6 hD1E)) (pow_ne_zero 5 hp1E)),
      rootMultiplicity_mul (mul_ne_zero (pow_ne_zero 2 hME) (pow_ne_zero 6 hD1E)),
      rootMultiplicity_pow_eq' _ hME 2 a, rootMultiplicity_pow_eq' _ hD1E 6 a,
      rootMultiplicity_pow_eq' _ hp1E 5 a,
      K.M0eff_rm_eq_mVal a, rootMultiplicity_comp_X_sq_map K.p1 K.hp1_ne a,
      rootMultiplicity_comp_X_sq_map K.Lam1 K.hLam1_ne a] at hle
    have hι : ι = algebraMap Fld (AlgebraicClosure Fld) := rfl
    rw [hι] at hle; dsimp [g, lam, d2, a1, g_l, lam_l, d2_l, a1_l, pt] at hle ⊢; omega
  have htot : c + e1 + pt.mVal = 2 * g + b := by
    have h1 := congrArg (fun f : Fld[X] => (f.map ι).rootMultiplicity a) K.HK_decomp
    simp only [Polynomial.map_mul, Polynomial.map_pow] at h1
    have hME := (Polynomial.map_ne_zero_iff ι.injective).mpr K.M0eff_ne
    have hg2E := (Polynomial.map_ne_zero_iff ι.injective).mpr D.g2_ne_zero
    have hgrE := (Polynomial.map_ne_zero_iff ι.injective).mpr K.g2rem_ne
    have hSKE := (Polynomial.map_ne_zero_iff ι.injective).mpr K.SK_ne
    have hHKE := (Polynomial.map_ne_zero_iff ι.injective).mpr K.HK_ne
    rw [rootMultiplicity_mul (mul_ne_zero (mul_ne_zero hME hg2E) hgrE),
      rootMultiplicity_mul (mul_ne_zero hME hg2E),
      rootMultiplicity_mul (mul_ne_zero (pow_ne_zero 2 hSKE) hHKE),
      rootMultiplicity_pow_eq' _ hSKE 2 a, K.M0eff_rm_eq_mVal a] at h1
    have hι : ι = algebraMap Fld (AlgebraicClosure Fld) := rfl
    rw [hι] at h1; dsimp [c, e1, g, b, c_l, e1_l, g_l, b_l, pt] at h1 ⊢; omega
  -- Prove vChat matches v(Q) - v(Hrem)!
  have hvChat_eq : pt.mbad = 0 → pt.vChat mu e1 c =
      ((K.Qpoly.map ι).rootMultiplicity a : ℤ) - ((K.Hrem.map ι).rootMultiplicity a : ℤ) := fun hmb0 => by
    rw [K.v_Q_sub_Hrem a]
    dsimp [mu, muEx_l, pt] at hmb0 ⊢
    cases hpt : K.ptOf a
    · simp only [hpt, muSub, Step15Pt.vChat, Step15Pt.isML, Step15Pt.nu, Step15Pt.mVal, Step15Pt.m0, Step15Pt.mbad, Step15Pt.m1, Step15Pt.m2, Bool.false_eq_true, ↓reduceIte]; rw [sub_zero_nr]; push_cast; ring
    · simp only [hpt, muSub, Step15Pt.vChat, Step15Pt.isML, Step15Pt.nu, Step15Pt.mVal, Step15Pt.m0, Step15Pt.mbad, Step15Pt.m1, Step15Pt.m2, Bool.false_eq_true, ↓reduceIte]; rw [sub_zero_nr]; push_cast; ring
    · simp only [hpt, muSub, Step15Pt.vChat, Step15Pt.isML, Step15Pt.nu, Step15Pt.mVal, Step15Pt.m0, Step15Pt.mbad, Step15Pt.m1, Step15Pt.m2, Bool.false_eq_true, ↓reduceIte]; rw [sub_zero_nr]; push_cast; ring
    · simp only [hpt, muSub, Step15Pt.vChat, Step15Pt.isML, Step15Pt.nu, Step15Pt.mVal, Step15Pt.m0, Step15Pt.mbad, Step15Pt.m1, Step15Pt.m2, Bool.false_eq_true, ↓reduceIte]; rw [sub_zero_nr]; push_cast; ring
    · have h1 := hmuRaw_ge1 (Or.inl hpt)
      simp only [hpt, muSub, Step15Pt.vChat, Step15Pt.isML, Step15Pt.nu, Step15Pt.mVal, Step15Pt.m0, Step15Pt.mbad, Step15Pt.m1, Step15Pt.m2, Bool.false_eq_true, ↓reduceIte]
      rw [Nat.cast_sub h1]; push_cast; ring
    · obtain ⟨i, hi⟩ := hdom_of_pt (by simp [pt, hpt])
      rw [hrm_dom_M0s i hi]
      have hmL : K.isML i := ((K.ptOf_dom_spec i).2.2.2.1 (hi ▸ hpt)).2
      have hm0 : K.M0s.rootMultiplicity (BinaryIRSProfile.domain i ^ 2) = 0 :=
        rootMultiplicity_eq_zero_iff.mpr (fun hr => absurd hr hmL.2.2.2)
      simp only [hpt, muSub, Step15Pt.vChat, Step15Pt.isML, Step15Pt.nu, Step15Pt.mVal, Step15Pt.m0, Step15Pt.mbad, Step15Pt.m1, Step15Pt.m2, ↓reduceIte]
      rw [hm0]; push_cast; ring
    · rw [hpt] at hmb0; exact False.elim (Nat.one_ne_zero hmb0)
    · have h1 := hmuRaw_ge1 (Or.inr hpt)
      simp only [hpt, muSub, Step15Pt.vChat, Step15Pt.isML, Step15Pt.nu, Step15Pt.mVal, Step15Pt.m0, Step15Pt.mbad, Step15Pt.m1, Step15Pt.m2, Bool.false_eq_true, ↓reduceIte]
      rw [Nat.cast_sub h1]; push_cast; ring
    · obtain ⟨i, hi⟩ := hdom_of_pt (by simp [pt, hpt])
      rw [hrm_dom_M0s i hi]
      have hmL : K.isML i := ((K.ptOf_dom_spec i).2.2.2.2.2.2.1 (hi ▸ hpt)).2
      have hm0 : K.M0s.rootMultiplicity (BinaryIRSProfile.domain i ^ 2) = 0 :=
        rootMultiplicity_eq_zero_iff.mpr (fun hr => absurd hr hmL.2.2.2)
      simp only [hpt, muSub, Step15Pt.vChat, Step15Pt.isML, Step15Pt.nu, Step15Pt.mVal, Step15Pt.m0, Step15Pt.mbad, Step15Pt.m1, Step15Pt.m2, ↓reduceIte]
      rw [hm0]; push_cast; ring
    · rw [hpt] at hmb0; exact False.elim (Nat.one_ne_zero hmb0)
  have hvChat_mb : pt.mbad = 1 → (c : ℤ) - (e1 : ℤ) - 1 - 2 * (mu : ℤ) =
      ((K.Qpoly.map ι).rootMultiplicity a : ℤ) - ((K.Hrem.map ι).rootMultiplicity a : ℤ) := fun hmb1 => by
    rw [K.v_Q_sub_Hrem a]
    dsimp [mu, muEx_l, pt] at hmb1 ⊢
    cases hpt : K.ptOf a
    · rw [hpt] at hmb1; exact False.elim (Nat.zero_ne_one hmb1)
    · rw [hpt] at hmb1; exact False.elim (Nat.zero_ne_one hmb1)
    · rw [hpt] at hmb1; exact False.elim (Nat.zero_ne_one hmb1)
    · rw [hpt] at hmb1; exact False.elim (Nat.zero_ne_one hmb1)
    · rw [hpt] at hmb1; exact False.elim (Nat.zero_ne_one hmb1)
    · rw [hpt] at hmb1; exact False.elim (Nat.zero_ne_one hmb1)
    · have h2 := (hmuRaw_mb (Or.inl hpt)).1
      simp only [hpt, muSub, Step15Pt.nu, Step15Pt.mVal, Step15Pt.m0, Step15Pt.mbad, Step15Pt.m1, Step15Pt.m2]
      rw [Nat.cast_sub h2]; push_cast; ring
    · rw [hpt] at hmb1; exact False.elim (Nat.zero_ne_one hmb1)
    · rw [hpt] at hmb1; exact False.elim (Nat.zero_ne_one hmb1)
    · have h2 := (hmuRaw_mb (Or.inr hpt)).1
      simp only [hpt, muSub, Step15Pt.nu, Step15Pt.mVal, Step15Pt.m0, Step15Pt.mbad, Step15Pt.m1, Step15Pt.m2]
      rw [Nat.cast_sub h2]; push_cast; ring
  refine ⟨hd2_le, hb_le, hL0_ev, hLnoU_ev, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hS_bound, htot,
    hvChat_eq, hvChat_mb, ?_⟩
  · -- hL0
    intro hpos; dsimp [L0, L0_l] at hpos; split_ifs at hpos with hex h3
    · have hi := Classical.choose_spec hex; set i := Classical.choose hex
      have hpt' := K.ptOf_dom i; rw [← hi] at hpt'
      have hk0 : D.k i ≠ 0 := by omega
      have hk1 : D.k i ≠ 1 := by omega
      have hk2 : D.k i ≠ 2 := by omega
      dsimp [pt]; rw [hpt']
      simp only [hk0, hk1, hk2, h3.2, not_true_eq_false, ↓reduceIte]
      by_cases hn : K.isNorm i
      · left; simp [hn]
      · by_cases hmL : K.isML i
        · right; left; simp [hn, hmL]
        · right; right; simp [hn, hmL]
    · omega
    · omega
  · -- hLnoU
    intro hpos; dsimp [LnoU, LnoU_l] at hpos; split_ifs at hpos with hex h3
    · have hi := Classical.choose_spec hex; set i := Classical.choose hex
      have hpt' := K.ptOf_dom i; rw [← hi] at hpt'
      have hk0 : D.k i ≠ 0 := by omega
      have hk1 : D.k i ≠ 1 := by omega
      dsimp [pt]; rw [hpt']; simp [hk0, hk1, h3.2]
    · omega
    · omega
  · -- hd2_zero
    intro hpt
    obtain ⟨i, hi⟩ := hdom_of_pt (by rcases hpt with h | h | h <;> simp [h])
    rw [hrm_dom_D1 i hi]
    have hsp := K.ptOf_dom_spec i
    rcases hpt with h | h | h
    · have hnotU : ¬ S.isU0 i := (hsp.2.1 (hi ▸ h)).2
      exact fun hD1 => hnotU (K.isU0_of_D1_zero hD1)
    · have hmb : K.g2t.eval (BinaryIRSProfile.domain i) ≠ 0 := (hsp.2.2.2.2.1 (hi ▸ h)).2.2.2
      exact fun hD1 => hmb (K.g2t_zero_of_D1_zero hD1)
    · have hmb : K.g2t.eval (BinaryIRSProfile.domain i) ≠ 0 := (hsp.2.2.2.2.2.2.2 (hi ▸ h)).2.2.2
      exact fun hD1 => hmb (K.g2t_zero_of_D1_zero hD1)
  · -- ha1_zero
    intro hpt hd0
    obtain ⟨i, hi⟩ := hdom_of_pt (by rcases hpt with h | h | h | h | h | h | h <;> simp [h])
    rw [hrm_dom_p1 i hi]
    have hD1_ne : ¬ K.isD1 i := (hrm_dom_D1 i hi).mp hd0
    have hsp := K.ptOf_dom_spec i
    have hU : S.isU0 i := by
      rcases hpt with h | h | h | h | h | h | h
      · exact (hsp.2.2.1 (hi ▸ h)).2.2.1
      · exact (hsp.2.2.2.1 (hi ▸ h)).2.2.1
      · exact (hsp.2.2.2.2.1 (hi ▸ h)).2.2.1
      · exact (hsp.2.2.2.2.2.1 (hi ▸ h)).2.2.1
      · exact (hsp.2.2.2.2.2.2.1 (hi ▸ h)).2.2.1
      · exact (hsp.2.2.2.2.2.2.2 (hi ▸ h)).2.2.1
      · exact (hsp.1 (hi ▸ h)).2
    exact K.p1_ne_zero_of_isU0_D1_ne hU hD1_ne
  · -- hmu_mL
    intro hpt
    obtain ⟨i, hi⟩ := hdom_of_pt (by rcases hpt with h | h <;> simp [h])
    have hsp := K.ptOf_dom_spec i
    have hmL : K.isML i := by
      rcases hpt with h | h
      · exact (hsp.2.2.2.1 (hi ▸ h)).2
      · exact (hsp.2.2.2.2.2.2.1 (hi ▸ h)).2
    dsimp [mu, muEx_l]; rw [hrm_dom_M0s i hi, rootMultiplicity_eq_zero_iff.mpr (fun hr => absurd hr hmL.2.2.2)]; exact Nat.zero_sub _
  · -- hk2noU
    intro hpt
    obtain ⟨i, hi⟩ := hdom_of_pt (by simp [hpt])
    have hk2 : 2 ≤ D.k i ∧ ¬ S.isU0 i := (K.ptOf_dom_spec i).2.1 (hi ▸ hpt)
    have hprod := K.pow_dvd_Lam1_mul_M0s i
    simp only [hk2.2, show D.k i ≠ 0 by omega, show D.k i ≠ 1 by omega, ↓reduceIte] at hprod
    have hrm := (le_rootMultiplicity_iff (mul_ne_zero K.hLam1_ne K.hM0s_ne)).mpr hprod
    rw [rootMultiplicity_mul (mul_ne_zero K.hLam1_ne K.hM0s_ne)] at hrm
    have hmu_eq : mu = K.M0s.rootMultiplicity (BinaryIRSProfile.domain i ^ 2) := by
      dsimp [mu, muEx_l]; rw [show K.ptOf a = .k2noU from hpt, hrm_dom_M0s i hi, show muSub .k2noU = 0 from rfl]; exact sub_zero_nr _
    rw [hrm_dom_Lam1 i hi, hmu_eq]
    have hLno_i : LnoU = if 3 ≤ D.k i ∧ ¬ S.isU0 i then 2 * (D.k i - 3) else 0 := by
      dsimp [LnoU, LnoU_l]; rw [dif_pos ⟨i, hi⟩]
      have hch : Classical.choose (⟨i, hi⟩ : ∃ j, a = ι (BinaryIRSProfile.domain j)) = i :=
        BinaryIRSProfile.domain.injective (ι.injective ((Classical.choose_spec (⟨i, hi⟩ : ∃ j, a = ι (BinaryIRSProfile.domain j))).symm.trans hi))
      rw [hch]
    exact ⟨fun _ => by omega, fun hpos => by split_ifs at hLno_i <;> omega⟩
  · -- hk2U_mL
    intro hpt
    obtain ⟨i, hi⟩ := hdom_of_pt (by simp [hpt])
    have hmL : D.k i = 2 ∧ K.isML i := (K.ptOf_dom_spec i).2.2.2.1 (hi ▸ hpt)
    have hprod := K.pow_dvd_Lam1_mul_M0s i
    simp only [hmL.2.2.1, hmL.1, show ¬ (2 ≤ 1) by omega, ↓reduceIte] at hprod
    have hrm := (le_rootMultiplicity_iff (mul_ne_zero K.hLam1_ne K.hM0s_ne)).mpr hprod
    rw [rootMultiplicity_mul (mul_ne_zero K.hLam1_ne K.hM0s_ne),
      rootMultiplicity_eq_zero_iff.mpr (fun hr => absurd hr hmL.2.2.2.2), add_zero] at hrm
    rw [hrm_dom_Lam1 i hi]; omega
  · -- hk3U
    intro hpt
    obtain ⟨i, hi⟩ := hdom_of_pt (by simp [hpt])
    have hk3 : 3 ≤ D.k i ∧ K.isNorm i := (K.ptOf_dom_spec i).2.2.2.2.2.1 (hi ▸ hpt)
    have hprod := K.pow_dvd_Lam1_mul_M0s i
    simp only [hk3.2.2.1, show ¬ D.k i ≤ 1 by omega, ↓reduceIte] at hprod
    have hrm := (le_rootMultiplicity_iff (mul_ne_zero K.hLam1_ne K.hM0s_ne)).mpr hprod
    rw [rootMultiplicity_mul (mul_ne_zero K.hLam1_ne K.hM0s_ne)] at hrm
    have hL0_i : L0 = 2 * (D.k i - 3) := by
      dsimp [L0, L0_l]; rw [dif_pos ⟨i, hi⟩]
      have hch : Classical.choose (⟨i, hi⟩ : ∃ j, a = ι (BinaryIRSProfile.domain j)) = i :=
        BinaryIRSProfile.domain.injective (ι.injective ((Classical.choose_spec (⟨i, hi⟩ : ∃ j, a = ι (BinaryIRSProfile.domain j))).symm.trans hi))
      rw [hch, if_pos ⟨hk3.1, hk3.2.2.1⟩]
    have hmu_eq : mu = K.M0s.rootMultiplicity (BinaryIRSProfile.domain i ^ 2) - 1 := by
      dsimp [mu, muEx_l]; rw [show K.ptOf a = .k3U from hpt, hrm_dom_M0s i hi]; rfl
    rw [hrm_dom_Lam1 i hi, hmu_eq, hL0_i]; omega
  · -- hk3U_mL
    intro hpt
    obtain ⟨i, hi⟩ := hdom_of_pt (by simp [hpt])
    have hk3 : 3 ≤ D.k i ∧ K.isML i := (K.ptOf_dom_spec i).2.2.2.2.2.2.1 (hi ▸ hpt)
    have hprod := K.pow_dvd_Lam1_mul_M0s i
    simp only [hk3.2.2.1, show ¬ D.k i ≤ 1 by omega, ↓reduceIte] at hprod
    have hrm := (le_rootMultiplicity_iff (mul_ne_zero K.hLam1_ne K.hM0s_ne)).mpr hprod
    rw [rootMultiplicity_mul (mul_ne_zero K.hLam1_ne K.hM0s_ne),
      rootMultiplicity_eq_zero_iff.mpr (fun hr => absurd hr hk3.2.2.2.2), add_zero] at hrm
    have hL0_i : L0 = 2 * (D.k i - 3) := by
      dsimp [L0, L0_l]; rw [dif_pos ⟨i, hi⟩]
      have hch : Classical.choose (⟨i, hi⟩ : ∃ j, a = ι (BinaryIRSProfile.domain j)) = i :=
        BinaryIRSProfile.domain.injective (ι.injective ((Classical.choose_spec (⟨i, hi⟩ : ∃ j, a = ι (BinaryIRSProfile.domain j))).symm.trans hi))
      rw [hch, if_pos ⟨hk3.1, hk3.2.2.1⟩]
    rw [hrm_dom_Lam1 i hi, hL0_i]; omega
  · -- hk3U_mb_mu
    intro hpt
    have h := (hmuRaw_mb (Or.inr hpt)).2 hpt
    dsimp [mu, muEx_l]; rw [show K.ptOf a = .k3U_mb from hpt]; dsimp only [muSub]; omega
  · -- he1_k1U
    intro hpt hcond
    obtain ⟨i, hi⟩ := hdom_of_pt (by simp [hpt])
    have hk1 : D.k i = 1 ∧ S.isU0 i := (K.ptOf_dom_spec i).1 (hi ▸ hpt)
    have hg2t_eq := hrm_dom_g2t i hi
    rw [show pt = .k1U from hpt] at hg2t_eq; simp [Step15Pt.nu, Step15Pt.mVal, Step15Pt.m0, Step15Pt.mbad, Step15Pt.m1, Step15Pt.m2] at hg2t_eq
    rcases hcond with hd1' | hmu0
    · have hD1 : K.isD1 i := by by_contra h; have := (hrm_dom_D1 i hi).mpr h; omega
      have h1 := (le_rootMultiplicity_iff K.hg2t_ne).mpr (by rw [pow_one]; exact dvd_iff_isRoot.mpr (K.g2t_zero_of_D1_zero hD1))
      omega
    · by_cases hD1 : K.isD1 i
      · have h1 := (le_rootMultiplicity_iff K.hg2t_ne).mpr (by rw [pow_one]; exact dvd_iff_isRoot.mpr (K.g2t_zero_of_D1_zero hD1))
        omega
      · have hM0 : K.M0s.eval (BinaryIRSProfile.domain i ^ 2) ≠ 0 := by
          have hm0 : K.M0s.rootMultiplicity (BinaryIRSProfile.domain i ^ 2) = 0 := by
            dsimp [mu, muEx_l] at hmu0; rw [show K.ptOf a = .k1U from hpt, hrm_dom_M0s i hi, show muSub .k1U = 0 from rfl, sub_zero_nr] at hmu0; exact hmu0
          exact fun hr => K.hM0s_ne ((rootMultiplicity_eq_zero_iff.mp hm0) hr)
        have hH1d : X - C (BinaryIRSProfile.domain i) ∣ S.H1 := by
          have := S.pow_dvd_H1_of_isU0 i hk1.2; rwa [hk1.1, pow_one] at this
        rw [K.hH1_fac] at hH1d
        have hcop : IsCoprime (X - C (BinaryIRSProfile.domain i)) (S.D1 ^ 4 * K.M0s.comp (X ^ 2)) := by
          have hne : (S.D1 ^ 4 * K.M0s.comp (X ^ 2)).eval (BinaryIRSProfile.domain i) ≠ 0 := by
            rw [eval_mul, eval_pow, eval_comp, eval_pow, eval_X]; exact mul_ne_zero (pow_ne_zero 4 hD1) hM0
          exact (Polynomial.irreducible_X_sub_C _).coprime_iff_not_dvd.mpr (mt dvd_iff_isRoot.mp hne)
        have h1 := (le_rootMultiplicity_iff K.hg2t_ne).mpr (by rw [pow_one]; exact hcop.dvd_of_dvd_mul_left hH1d)
        omega
  · -- he1_mL
    intro hpt hd0
    obtain ⟨i, hi⟩ := hdom_of_pt (by rcases hpt with h | h <;> simp [h])
    have hD1 : ¬ K.isD1 i := (hrm_dom_D1 i hi).mp hd0
    have hsp := K.ptOf_dom_spec i
    have hmL : K.isML i := by
      rcases hpt with h | h
      · exact (hsp.2.2.2.1 (hi ▸ h)).2
      · exact (hsp.2.2.2.2.2.2.1 (hi ▸ h)).2
    have hH1d := (pow_dvd_pow (X - C (BinaryIRSProfile.domain i)) (by have := hmL.1; omega : 3 ≤ 2 * D.k i - 1)).trans
      (S.pow_dvd_H1_of_isU0 i hmL.2.1)
    rw [K.hH1_fac] at hH1d
    have hcop : IsCoprime ((X - C (BinaryIRSProfile.domain i)) ^ 3) (S.D1 ^ 4 * K.M0s.comp (X ^ 2)) := by
      apply IsCoprime.pow_left
      have hne : (S.D1 ^ 4 * K.M0s.comp (X ^ 2)).eval (BinaryIRSProfile.domain i) ≠ 0 := by
        rw [eval_mul, eval_pow, eval_comp, eval_pow, eval_X]; exact mul_ne_zero (pow_ne_zero 4 hD1) hmL.2.2.2
      exact (Polynomial.irreducible_X_sub_C _).coprime_iff_not_dvd.mpr (mt dvd_iff_isRoot.mp hne)
    have h3 := (le_rootMultiplicity_iff K.hg2t_ne).mpr (hcop.dvd_of_dvd_mul_left hH1d)
    have hg2t_eq := hrm_dom_g2t i hi
    rcases hpt with h | h <;> rw [h] at hg2t_eq <;>
      simp [Step15Pt.nu, Step15Pt.mVal, Step15Pt.m0, Step15Pt.mbad, Step15Pt.m1, Step15Pt.m2] at hg2t_eq <;> omega
  · -- htri: universal 4-term valuation triangle from K.h4term_y0!
    intro hcond
    let y0 : Fld := if h : ∃ i : Idx, a = ι (BinaryIRSProfile.domain i) then D.y (Classical.choose h) else 0
    let Uy0 : Fld[X] := S.p.comp (X ^ 2) * C y0 + S.R
    let U1_y0 : Fld[X] := S.D1 * K.p1.comp (X ^ 2) * C y0 + K.R1
    let gsh0 : Fld[X] := D.gj 0 + C (y0 ^ 2) * D.gj 1 + C (y0 ^ 4) * D.gj 2
    have hUfac : Uy0 = S.D1 * U1_y0 := by
      dsimp [Uy0, U1_y0]; rw [K.hp_fac, mul_comp, ← S.D1_sq, K.hR_fac]; ring
    -- First show (U1_y0.map ι).eval a ≠ 0!
    have hU1_ev : (U1_y0.map ι).eval a ≠ 0 := by
      have hR1_ev_of_q1 : (K.q1.map ι).eval (a ^ 2) ≠ 0 → (K.R1.map ι).eval a ≠ 0 := fun hq1 hR1 => by
        have h := congrArg (fun f : Fld[X] => (f.map ι).eval a) K.hR1_sq
        simp only [Polynomial.map_pow, Polynomial.map_comp, Polynomial.map_X, eval_pow, eval_comp, eval_X, hR1,
          zero_pow (show (2 : ℕ) ≠ 0 by norm_num)] at h
        exact hq1 h.symm
      rcases hcond with ha1 | hd2' | hk2no
      · by_cases hd0 : d2 = 0
        · have hp10 : (K.p1.map ι).eval (a ^ 2) = 0 := by
            have := (pow_dvd_pow (X - C (a ^ 2)) ha1).trans (pow_rootMultiplicity_dvd (K.p1.map ι) (a ^ 2))
            rw [pow_one] at this; exact dvd_iff_isRoot.mp this
          have hq1_ne : (K.q1.map ι).eval (a ^ 2) ≠ 0 := fun hq10 => by
            have hu := (K.hp1_q1_cop.map (Polynomial.mapRingHom ι)).isUnit_of_dvd' (dvd_iff_isRoot.mpr hp10) (dvd_iff_isRoot.mpr hq10)
            have h0 := natDegree_eq_zero_of_isUnit hu; rw [natDegree_X_sub_C] at h0; omega
          have hR1_ne := hR1_ev_of_q1 hq1_ne
          dsimp [U1_y0]
          simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_comp, Polynomial.map_pow, Polynomial.map_X,
            Polynomial.map_C, eval_add, eval_mul, eval_comp, eval_pow, eval_X, eval_C, hp10, mul_zero, zero_mul, zero_add]
          exact hR1_ne
        · have hD10 : (S.D1.map ι).eval a = 0 := by
            have := (pow_dvd_pow (X - C a) (by omega : 1 ≤ d2)).trans (pow_rootMultiplicity_dvd (S.D1.map ι) a)
            rw [pow_one] at this; exact dvd_iff_isRoot.mp this
          have hD20 : (S.D2.map ι).eval (a ^ 2) = 0 := by
            have h := congrArg (fun f : Fld[X] => (f.map ι).eval a) S.D1_sq
            simp only [Polynomial.map_pow, Polynomial.map_comp, Polynomial.map_X, eval_pow, eval_comp, eval_X, hD10,
              zero_pow (show (2 : ℕ) ≠ 0 by norm_num)] at h
            exact h.symm
          have hq1_ne : (K.q1.map ι).eval (a ^ 2) ≠ 0 := fun hq10 => by
            have hu := (K.hD2_q1_cop.map (Polynomial.mapRingHom ι)).isUnit_of_dvd' (dvd_iff_isRoot.mpr hD20) (dvd_iff_isRoot.mpr hq10)
            have h0 := natDegree_eq_zero_of_isUnit hu; rw [natDegree_X_sub_C] at h0; omega
          have hR1_ne := hR1_ev_of_q1 hq1_ne
          dsimp [U1_y0]
          simp only [Polynomial.map_add, Polynomial.map_mul, eval_add, eval_mul, hD10, zero_mul, zero_add]
          exact hR1_ne
      · have hD10 : (S.D1.map ι).eval a = 0 := by
          have := (pow_dvd_pow (X - C a) hd2').trans (pow_rootMultiplicity_dvd (S.D1.map ι) a)
          rw [pow_one] at this; exact dvd_iff_isRoot.mp this
        have hD20 : (S.D2.map ι).eval (a ^ 2) = 0 := by
          have h := congrArg (fun f : Fld[X] => (f.map ι).eval a) S.D1_sq
          simp only [Polynomial.map_pow, Polynomial.map_comp, Polynomial.map_X, eval_pow, eval_comp, eval_X, hD10,
            zero_pow (show (2 : ℕ) ≠ 0 by norm_num)] at h
          exact h.symm
        have hq1_ne : (K.q1.map ι).eval (a ^ 2) ≠ 0 := fun hq10 => by
          have hu := (K.hD2_q1_cop.map (Polynomial.mapRingHom ι)).isUnit_of_dvd' (dvd_iff_isRoot.mpr hD20) (dvd_iff_isRoot.mpr hq10)
          have h0 := natDegree_eq_zero_of_isUnit hu; rw [natDegree_X_sub_C] at h0; omega
        have hR1_ne := hR1_ev_of_q1 hq1_ne
        dsimp [U1_y0]
        simp only [Polynomial.map_add, Polynomial.map_mul, eval_add, eval_mul, hD10, zero_mul, zero_add]
        exact hR1_ne
      · obtain ⟨i, hi⟩ := hdom_of_pt (by simp [hk2no])
        have hnotU : ¬ S.isU0 i := ((K.ptOf_dom_spec i).2.1 (hi ▸ hk2no)).2
        have hy0_i : y0 = D.y i := by
          dsimp [y0]; rw [dif_pos ⟨i, hi⟩]
          have hch : Classical.choose (⟨i, hi⟩ : ∃ j, a = ι (BinaryIRSProfile.domain j)) = i :=
            BinaryIRSProfile.domain.injective (ι.injective ((Classical.choose_spec (⟨i, hi⟩ : ∃ j, a = ι (BinaryIRSProfile.domain j))).symm.trans hi))
          rw [hch]
        have hUy_ne : (Uy0.map ι).eval a ≠ 0 := by
          rw [hi, eval_map_apply]; intro h0; apply hnotU
          have h0' : Uy0.eval (BinaryIRSProfile.domain i) = 0 := ι.injective (by rw [map_zero]; exact h0)
          simpa [Uy0, hy0_i, KerD45Syzygy.isU0, KerD45Syzygy.U_eval] using h0'
        intro hU10; apply hUy_ne; rw [hUfac, Polynomial.map_mul, eval_mul, hU10, mul_zero]
    have hU1_ne : U1_y0.map ι ≠ 0 := fun h0 => hU1_ev (by rw [h0, eval_zero])
    have hU1_rm0 : (U1_y0.map ι).rootMultiplicity a = 0 := rootMultiplicity_eq_zero_iff.mpr (fun hr => absurd hr hU1_ev)
    -- Apply tri_of_four_term_id to K.h4term_y0 y0 mapped to E!
    let T1 : E[X] := ((S.D1 ^ 4 * K.p1.comp (X ^ 2) ^ 4 * gsh0).map ι)
    let T2 : E[X] := ((K.p1.comp (X ^ 2) ^ 2 * Uy0 ^ 2 * D.gj 1).map ι)
    let T3 : E[X] := ((K.M0s.comp (X ^ 2) * K.g2t).map ι)
    let T4 : E[X] := ((D.gj 2 * U1_y0 ^ 4).map ι)
    have hT3_ne : T3 ≠ 0 := (Polynomial.map_ne_zero_iff ι.injective).mpr
      (mul_ne_zero (mt (comp_X_sq_eq_zero_iff K.M0s).mp K.hM0s_ne) K.hg2t_ne)
    have hT4_ne : T4 ≠ 0 := by
      dsimp [T4]; rw [Polynomial.map_mul, Polynomial.map_pow]
      exact mul_ne_zero ((Polynomial.map_ne_zero_iff ι.injective).mpr D.g2_ne_zero) (pow_ne_zero 4 hU1_ne)
    have hidE : T1 + T2 + T3 = T4 := by
      have h := congrArg (Polynomial.map ι) (K.h4term_y0 y0)
      dsimp [T1, T2, T3, T4, gsh0, Uy0, U1_y0]
      simp only [Polynomial.map_add] at h
      linear_combination h
    -- Exact valuations of T3 and T4!
    have hT4_rm : T4.rootMultiplicity a = c := by
      dsimp [T4, c, c_l]; rw [Polynomial.map_mul, Polynomial.map_pow,
        rootMultiplicity_mul (mul_ne_zero ((Polynomial.map_ne_zero_iff ι.injective).mpr D.g2_ne_zero) (pow_ne_zero 4 hU1_ne)),
        rootMultiplicity_pow_eq' _ hU1_ne 4 a, hU1_rm0, mul_zero, add_zero]
    have hT3_rm : T3.rootMultiplicity a = pt.t3 d2 mu e1 - 3 * pt.mVal := by
      have hMcE := (Polynomial.map_ne_zero_iff ι.injective).mpr (mt (comp_X_sq_eq_zero_iff K.M0s).mp K.hM0s_ne)
      have hSgE := (Polynomial.map_ne_zero_iff ι.injective).mpr K.Sg2_ne
      have hgrE := (Polynomial.map_ne_zero_iff ι.injective).mpr K.g2rem_ne
      dsimp [T3]; rw [K.g2t_eq_Sg2_mul_g2rem, Polynomial.map_mul, Polynomial.map_mul,
        rootMultiplicity_mul (mul_ne_zero hMcE (mul_ne_zero hSgE hgrE)),
        rootMultiplicity_mul (mul_ne_zero hSgE hgrE),
        rootMultiplicity_comp_X_sq_map K.M0s K.hM0s_ne a, K.Sg2_rm_eq a]
      -- Note mbad cannot occur under hcond (since mbad has d2 = 0 and a1 = 0)!
      have hnmb : pt ≠ .k2U_mb ∧ pt ≠ .k3U_mb := by
        constructor <;> intro hpt
        · obtain ⟨i, hi⟩ := hdom_of_pt (by simp [hpt])
          have hmb : K.isMbad i := ((K.ptOf_dom_spec i).2.2.2.2.1 (hi ▸ hpt)).2
          have hd0 : d2 = 0 := (hrm_dom_D1 i hi).mpr (fun hD1 => hmb.2.2 (K.g2t_zero_of_D1_zero hD1))
          have ha0 : a1 = 0 := (hrm_dom_p1 i hi).mpr (K.p1_ne_zero_of_isU0_D1_ne hmb.2.1 ((hrm_dom_D1 i hi).mp hd0))
          rcases hcond with h | h | h
          · omega
          · omega
          · rw [hpt] at h; cases h
        · obtain ⟨i, hi⟩ := hdom_of_pt (by simp [hpt])
          have hmb : K.isMbad i := ((K.ptOf_dom_spec i).2.2.2.2.2.2.2 (hi ▸ hpt)).2
          have hd0 : d2 = 0 := (hrm_dom_D1 i hi).mpr (fun hD1 => hmb.2.2 (K.g2t_zero_of_D1_zero hD1))
          have ha0 : a1 = 0 := (hrm_dom_p1 i hi).mpr (K.p1_ne_zero_of_isU0_D1_ne hmb.2.1 ((hrm_dom_D1 i hi).mp hd0))
          rcases hcond with h | h | h
          · omega
          · omega
          · rw [hpt] at h; cases h
      have hd1_mL : (pt = .k2U_mL ∨ pt = .k3U_mL) → d2 = 1 := fun hpt => by
        by_contra hd0'
        have hd0 : d2 = 0 := by omega
        obtain ⟨i, hi⟩ := hdom_of_pt (by rcases hpt with h | h <;> simp [h])
        have hD1_ne := (hrm_dom_D1 i hi).mp hd0
        have hU : S.isU0 i := by
          rcases hpt with h | h
          · exact ((K.ptOf_dom_spec i).2.2.2.1 (hi ▸ h)).2.2.1
          · exact ((K.ptOf_dom_spec i).2.2.2.2.2.2.1 (hi ▸ h)).2.2.1
        have ha0 : a1 = 0 := (hrm_dom_p1 i hi).mpr (K.p1_ne_zero_of_isU0_D1_ne hU hD1_ne)
        rcases hcond with h | h | h
        · omega
        · omega
        · rcases hpt with hp | hp <;> rw [hp] at h <;> cases h
      have hι : ι = algebraMap Fld (AlgebraicClosure Fld) := rfl
      dsimp [mu, muEx_l, muRaw_l, e1, e1_l, pt] at hnmb hd1_mL ⊢; rw [hι]
      cases hpt : K.ptOf a
      · simp only [muSub, Step15Pt.t3, Step15Pt.isML, Step15Pt.nu, Step15Pt.mVal, Step15Pt.m0, Step15Pt.mbad, Step15Pt.m1, Step15Pt.m2, Bool.false_eq_true, false_and, ↓reduceIte]; rw [sub_zero_nr]; omega
      · simp only [muSub, Step15Pt.t3, Step15Pt.isML, Step15Pt.nu, Step15Pt.mVal, Step15Pt.m0, Step15Pt.mbad, Step15Pt.m1, Step15Pt.m2, Bool.false_eq_true, false_and, ↓reduceIte]; rw [sub_zero_nr]; omega
      · simp only [muSub, Step15Pt.t3, Step15Pt.isML, Step15Pt.nu, Step15Pt.mVal, Step15Pt.m0, Step15Pt.mbad, Step15Pt.m1, Step15Pt.m2, Bool.false_eq_true, false_and, ↓reduceIte]; rw [sub_zero_nr]; omega
      · simp only [muSub, Step15Pt.t3, Step15Pt.isML, Step15Pt.nu, Step15Pt.mVal, Step15Pt.m0, Step15Pt.mbad, Step15Pt.m1, Step15Pt.m2, Bool.false_eq_true, false_and, ↓reduceIte]; rw [sub_zero_nr]; omega
      · have h1 := hmuRaw_ge1 (Or.inl hpt); dsimp [muRaw_l] at h1
        simp only [muSub, Step15Pt.t3, Step15Pt.isML, Step15Pt.nu, Step15Pt.mVal, Step15Pt.m0, Step15Pt.mbad, Step15Pt.m1, Step15Pt.m2, Bool.false_eq_true, false_and, ↓reduceIte]; omega
      · have hd1' := hd1_mL (Or.inl hpt)
        obtain ⟨i, hi⟩ := hdom_of_pt (by simp [pt, hpt])
        have hmL : K.isML i := ((K.ptOf_dom_spec i).2.2.2.1 (hi ▸ hpt)).2
        have hm0 : (K.M0s.map (algebraMap Fld (AlgebraicClosure Fld))).rootMultiplicity (a ^ 2) = 0 := by
          rw [← hι, hi, ← map_pow, rootMultiplicity_map_eq]; exact rootMultiplicity_eq_zero_iff.mpr (fun hr => absurd hr hmL.2.2.2)
        simp only [hd1', hm0, muSub, Step15Pt.t3, Step15Pt.isML, Step15Pt.nu, Step15Pt.mVal, Step15Pt.m0, Step15Pt.mbad, Step15Pt.m1, Step15Pt.m2, and_self, ↓reduceIte]; omega
      · exact absurd hpt hnmb.1
      · have h1 := hmuRaw_ge1 (Or.inr hpt); dsimp [muRaw_l] at h1
        simp only [muSub, Step15Pt.t3, Step15Pt.isML, Step15Pt.nu, Step15Pt.mVal, Step15Pt.m0, Step15Pt.mbad, Step15Pt.m1, Step15Pt.m2, Bool.false_eq_true, false_and, ↓reduceIte]; omega
      · have hd1' := hd1_mL (Or.inr hpt)
        obtain ⟨i, hi⟩ := hdom_of_pt (by simp [pt, hpt])
        have hmL : K.isML i := ((K.ptOf_dom_spec i).2.2.2.2.2.2.1 (hi ▸ hpt)).2
        have hm0 : (K.M0s.map (algebraMap Fld (AlgebraicClosure Fld))).rootMultiplicity (a ^ 2) = 0 := by
          rw [← hι, hi, ← map_pow, rootMultiplicity_map_eq]; exact rootMultiplicity_eq_zero_iff.mpr (fun hr => absurd hr hmL.2.2.2)
        simp only [hd1', hm0, muSub, Step15Pt.t3, Step15Pt.isML, Step15Pt.nu, Step15Pt.mVal, Step15Pt.m0, Step15Pt.mbad, Step15Pt.m1, Step15Pt.m2, and_self, ↓reduceIte]; omega
      · exact absurd hpt hnmb.2
    -- Divisibility bounds on T1 and T2!
    have hd_T1 : (X - C a) ^ (8 * a1 + 4 * d2 + pt.vc0 d2 e1 c L0 LnoU) ∣ T1 := by
      dsimp [T1]; simp only [Polynomial.map_mul, Polynomial.map_pow]
      have hdD : (X - C a) ^ (4 * d2) ∣ (S.D1.map ι) ^ 4 := by
        rw [mul_comm 4 d2, pow_mul]; exact pow_dvd_pow_of_dvd (pow_rootMultiplicity_dvd (S.D1.map ι) a) 4
      have hdp : (X - C a) ^ (8 * a1) ∣ ((K.p1.comp (X ^ 2)).map ι) ^ 4 := by
        have h2a := pow_rootMultiplicity_dvd ((K.p1.comp (X ^ 2)).map ι) a
        rw [rootMultiplicity_comp_X_sq_map K.p1 K.hp1_ne a] at h2a
        rw [show 8 * a1 = (2 * a1) * 4 by ring, pow_mul]; exact pow_dvd_pow_of_dvd h2a 4
      have hdg : (X - C a) ^ (pt.vc0 d2 e1 c L0 LnoU) ∣ gsh0.map ι := by
        have hdom_g : ∀ i : Idx, a = ι (BinaryIRSProfile.domain i) → (X - C a) ^ (2 * D.k i - 1) ∣ gsh0.map ι := fun i hi => by
          have hy0_i : y0 = D.y i := by
            dsimp [y0]; rw [dif_pos ⟨i, hi⟩]
            have hch : Classical.choose (⟨i, hi⟩ : ∃ j, a = ι (BinaryIRSProfile.domain j)) = i :=
              BinaryIRSProfile.domain.injective (ι.injective ((Classical.choose_spec (⟨i, hi⟩ : ∃ j, a = ι (BinaryIRSProfile.domain j))).symm.trans hi))
            rw [hch]
          rcases K.pow_dvd_gsh0 i with ⟨w, hw⟩
          refine ⟨w.map ι, ?_⟩
          have h := congrArg (Polynomial.map ι) hw
          simpa [gsh0, hy0_i, hi] using h
        cases hpt : K.ptOf a
        · rw [show pt = .out from hpt, show Step15Pt.vc0 .out d2 e1 c L0 LnoU = 0 from rfl, pow_zero]; exact one_dvd _
        · rw [show pt = .k0 from hpt, show Step15Pt.vc0 .k0 d2 e1 c L0 LnoU = 0 from rfl, pow_zero]; exact one_dvd _
        · obtain ⟨i, hi⟩ := hdom_of_pt (by simp [pt, hpt])
          have hk1 : D.k i = 1 := ((K.ptOf_dom_spec i).1 (hi ▸ hpt)).1
          rw [show pt = .k1U from hpt, show Step15Pt.vc0 .k1U d2 e1 c L0 LnoU = 1 from rfl]
          have hg := hdom_g i hi; rw [hk1] at hg; exact hg
        · obtain ⟨i, hi⟩ := hdom_of_pt (by simp [pt, hpt])
          have hk2 : 2 ≤ D.k i ∧ ¬ S.isU0 i := (K.ptOf_dom_spec i).2.1 (hi ▸ hpt)
          have hLno_i : LnoU = if 3 ≤ D.k i ∧ ¬ S.isU0 i then 2 * (D.k i - 3) else 0 := by
            dsimp [LnoU, LnoU_l]; rw [dif_pos ⟨i, hi⟩]
            have hch : Classical.choose (⟨i, hi⟩ : ∃ j, a = ι (BinaryIRSProfile.domain j)) = i :=
              BinaryIRSProfile.domain.injective (ι.injective ((Classical.choose_spec (⟨i, hi⟩ : ∃ j, a = ι (BinaryIRSProfile.domain j))).symm.trans hi))
            rw [hch]
          refine (pow_dvd_pow _ ?_).trans (hdom_g i hi)
          rw [show pt = .k2noU from hpt]; dsimp only [Step15Pt.vc0]
          split_ifs with hpos
          · rw [hLno_i] at hpos ⊢
            split_ifs at hpos ⊢ with h3
            · have h3' := h3.1; generalize D.k i = ki at h3' ⊢; omega
            · exact absurd hpos (by decide)
          · have h2' := hk2.1; generalize D.k i = ki at h2' ⊢; omega
        · obtain ⟨i, hi⟩ := hdom_of_pt (by simp [pt, hpt])
          have hk2 : D.k i = 2 := ((K.ptOf_dom_spec i).2.2.1 (hi ▸ hpt)).1
          refine (pow_dvd_pow _ ?_).trans (hdom_g i hi)
          rw [show pt = .k2U from hpt, hk2]; dsimp only [Step15Pt.vc0]
          split_ifs
          · exact le_rfl
          · exact Nat.min_le_left 3 _
        · obtain ⟨i, hi⟩ := hdom_of_pt (by simp [pt, hpt])
          have hk2 : D.k i = 2 := ((K.ptOf_dom_spec i).2.2.2.1 (hi ▸ hpt)).1
          refine (pow_dvd_pow _ ?_).trans (hdom_g i hi)
          rw [show pt = .k2U_mL from hpt, hk2]; dsimp only [Step15Pt.vc0]
          split_ifs
          · exact le_rfl
          · exact Nat.min_le_left 3 _
        · rw [show pt = .k2U_mb from hpt, show Step15Pt.vc0 .k2U_mb d2 e1 c L0 LnoU = 0 from rfl, pow_zero]; exact one_dvd _
        · obtain ⟨i, hi⟩ := hdom_of_pt (by simp [pt, hpt])
          have hsp := (K.ptOf_dom_spec i).2.2.2.2.2.1 (hi ▸ hpt)
          have hk3 : 3 ≤ D.k i ∧ S.isU0 i := ⟨hsp.1, hsp.2.2.1⟩
          have hL0_i : L0 = 2 * (D.k i - 3) := by
            dsimp [L0, L0_l]; rw [dif_pos ⟨i, hi⟩]
            have hch : Classical.choose (⟨i, hi⟩ : ∃ j, a = ι (BinaryIRSProfile.domain j)) = i :=
              BinaryIRSProfile.domain.injective (ι.injective ((Classical.choose_spec (⟨i, hi⟩ : ∃ j, a = ι (BinaryIRSProfile.domain j))).symm.trans hi))
            rw [hch, if_pos hk3]
          refine (pow_dvd_pow _ ?_).trans (hdom_g i hi)
          rw [show pt = .k3U from hpt]; dsimp only [Step15Pt.vc0]
          split_ifs
          · rw [hL0_i]; have h3' := hk3.1; generalize D.k i = ki at h3' ⊢; omega
          · exact (Nat.min_le_left 3 _).trans (by have h3' := hk3.1; generalize D.k i = ki at h3' ⊢; omega)
        · obtain ⟨i, hi⟩ := hdom_of_pt (by simp [pt, hpt])
          have hsp := (K.ptOf_dom_spec i).2.2.2.2.2.2.1 (hi ▸ hpt)
          have hk3 : 3 ≤ D.k i ∧ S.isU0 i := ⟨hsp.1, hsp.2.2.1⟩
          have hL0_i : L0 = 2 * (D.k i - 3) := by
            dsimp [L0, L0_l]; rw [dif_pos ⟨i, hi⟩]
            have hch : Classical.choose (⟨i, hi⟩ : ∃ j, a = ι (BinaryIRSProfile.domain j)) = i :=
              BinaryIRSProfile.domain.injective (ι.injective ((Classical.choose_spec (⟨i, hi⟩ : ∃ j, a = ι (BinaryIRSProfile.domain j))).symm.trans hi))
            rw [hch, if_pos hk3]
          refine (pow_dvd_pow _ ?_).trans (hdom_g i hi)
          rw [show pt = .k3U_mL from hpt]; dsimp only [Step15Pt.vc0]
          split_ifs
          · rw [hL0_i]; have h3' := hk3.1; generalize D.k i = ki at h3' ⊢; omega
          · exact (Nat.min_le_left 3 _).trans (by have h3' := hk3.1; generalize D.k i = ki at h3' ⊢; omega)
        · rw [show pt = .k3U_mb from hpt, show Step15Pt.vc0 .k3U_mb d2 e1 c L0 LnoU = 0 from rfl, pow_zero]; exact one_dvd _
      rw [show 8 * a1 + 4 * d2 + pt.vc0 d2 e1 c L0 LnoU = 4 * d2 + 8 * a1 + pt.vc0 d2 e1 c L0 LnoU by omega,
        pow_add, pow_add]
      exact mul_dvd_mul (mul_dvd_mul hdD hdp) hdg
    have hd_T2 : (X - C a) ^ (4 * a1 + 2 * d2 + 2 * pt.k1Min d2 lam L0 LnoU + (pt.nu - pt.mVal) + e1) ∣ T2 := by
      dsimp [T2]; rw [K.hg1_fac, K.g2t_eq_Sg2_mul_g2rem, hUfac]
      simp only [Polynomial.map_mul, Polynomial.map_pow]
      have hdp : (X - C a) ^ (4 * a1) ∣ ((K.p1.comp (X ^ 2)).map ι) ^ 2 := by
        have h2a := pow_rootMultiplicity_dvd ((K.p1.comp (X ^ 2)).map ι) a
        rw [rootMultiplicity_comp_X_sq_map K.p1 K.hp1_ne a] at h2a
        rw [show 4 * a1 = (2 * a1) * 2 by ring, pow_mul]; exact pow_dvd_pow_of_dvd h2a 2
      have hdU : (X - C a) ^ (2 * d2) ∣ (S.D1.map ι * U1_y0.map ι) ^ 2 := by
        rw [mul_pow, mul_comm 2 d2, pow_mul]
        exact dvd_mul_of_dvd_left (pow_dvd_pow_of_dvd (pow_rootMultiplicity_dvd (S.D1.map ι) a) 2) _
      have hdK1 : (X - C a) ^ (2 * pt.k1Min d2 lam L0 LnoU) ∣ (K.K1.comp (X ^ 2)).map ι := by
        have h2k := pow_rootMultiplicity_dvd ((K.K1.comp (X ^ 2)).map ι) a
        rw [rootMultiplicity_comp_X_sq_map K.K1 K.hK1_ne a] at h2k
        refine (pow_dvd_pow _ (Nat.mul_le_mul_left 2 ?_)).trans h2k
        cases hpt : K.ptOf a
        · rw [show pt = .out from hpt, show Step15Pt.k1Min .out d2 lam L0 LnoU = 0 from rfl]; exact Nat.zero_le _
        · rw [show pt = .k0 from hpt, show Step15Pt.k1Min .k0 d2 lam L0 LnoU = 0 from rfl]; exact Nat.zero_le _
        · rw [show pt = .k1U from hpt, show Step15Pt.k1Min .k1U d2 lam L0 LnoU = 0 from rfl]; exact Nat.zero_le _
        · obtain ⟨i, hi⟩ := hdom_of_pt (by simp [pt, hpt])
          have hk2 : 2 ≤ D.k i ∧ ¬ S.isU0 i := (K.ptOf_dom_spec i).2.1 (hi ▸ hpt)
          have hLno_i : LnoU = if 3 ≤ D.k i ∧ ¬ S.isU0 i then 2 * (D.k i - 3) else 0 := by
            dsimp [LnoU, LnoU_l]; rw [dif_pos ⟨i, hi⟩]
            have hch : Classical.choose (⟨i, hi⟩ : ∃ j, a = ι (BinaryIRSProfile.domain j)) = i :=
              BinaryIRSProfile.domain.injective (ι.injective ((Classical.choose_spec (⟨i, hi⟩ : ∃ j, a = ι (BinaryIRSProfile.domain j))).symm.trans hi))
            rw [hch]
          have hrm := (le_rootMultiplicity_iff K.hK1_ne).mpr (K.pow_dvd_K1_U1 i hk2.2)
          rw [hi, ← map_pow, rootMultiplicity_map_eq, show pt = .k2noU from hpt]; dsimp only [Step15Pt.k1Min]
          split_ifs with hpos
          · rw [hLno_i] at hpos ⊢
            split_ifs at hpos ⊢ with h3
            · have h3' := h3.1; generalize D.k i = ki at h3' hrm ⊢; generalize K.K1.rootMultiplicity (BinaryIRSProfile.domain i ^ 2) = rm at hrm ⊢; omega
            · exact absurd hpos (Nat.not_lt_zero 0)
          · have h2' := hk2.1; generalize D.k i = ki at h2' hrm ⊢; generalize K.K1.rootMultiplicity (BinaryIRSProfile.domain i ^ 2) = rm at hrm ⊢; omega
        · obtain ⟨i, hi⟩ := hdom_of_pt (by simp [pt, hpt])
          have hk2 : D.k i = 2 := ((K.ptOf_dom_spec i).2.2.1 (hi ▸ hpt)).1
          rw [show pt = .k2U from hpt]; dsimp only [Step15Pt.k1Min]; split_ifs with hd1'
          · have hD1 : K.isD1 i := by by_contra h; have := (hrm_dom_D1 i hi).mpr h; omega
            have hKL := K.pow_dvd_K_M10sh_d2 i hD1
            simp only [hk2, show ¬ (2 ≤ 1) by omega, ↓reduceIte] at hKL
            have hrm := (le_rootMultiplicity_iff (mul_ne_zero K.hK1_ne K.hLam1_ne)).mpr hKL
            rw [rootMultiplicity_mul (mul_ne_zero K.hK1_ne K.hLam1_ne)] at hrm
            rw [hi, ← map_pow, rootMultiplicity_map_eq, hrm_dom_Lam1 i hi]
            generalize K.K1.rootMultiplicity (BinaryIRSProfile.domain i ^ 2) = r1 at hrm ⊢
            generalize K.Lam1.rootMultiplicity (BinaryIRSProfile.domain i ^ 2) = r2 at hrm ⊢; omega
          · exact Nat.zero_le _
        · obtain ⟨i, hi⟩ := hdom_of_pt (by simp [pt, hpt])
          have hk2 : D.k i = 2 := ((K.ptOf_dom_spec i).2.2.2.1 (hi ▸ hpt)).1
          rw [show pt = .k2U_mL from hpt]; dsimp only [Step15Pt.k1Min]; split_ifs with hd1'
          · have hD1 : K.isD1 i := by by_contra h; have := (hrm_dom_D1 i hi).mpr h; omega
            have hKL := K.pow_dvd_K_M10sh_d2 i hD1
            simp only [hk2, show ¬ (2 ≤ 1) by omega, ↓reduceIte] at hKL
            have hrm := (le_rootMultiplicity_iff (mul_ne_zero K.hK1_ne K.hLam1_ne)).mpr hKL
            rw [rootMultiplicity_mul (mul_ne_zero K.hK1_ne K.hLam1_ne)] at hrm
            rw [hi, ← map_pow, rootMultiplicity_map_eq, hrm_dom_Lam1 i hi]
            generalize K.K1.rootMultiplicity (BinaryIRSProfile.domain i ^ 2) = r1 at hrm ⊢
            generalize K.Lam1.rootMultiplicity (BinaryIRSProfile.domain i ^ 2) = r2 at hrm ⊢; omega
          · exact Nat.zero_le _
        · rw [show pt = .k2U_mb from hpt, show Step15Pt.k1Min .k2U_mb d2 lam L0 LnoU = 0 from rfl]; exact Nat.zero_le _
        · obtain ⟨i, hi⟩ := hdom_of_pt (by simp [pt, hpt])
          have hsp := (K.ptOf_dom_spec i).2.2.2.2.2.1 (hi ▸ hpt)
          have hk3 : 3 ≤ D.k i ∧ S.isU0 i := ⟨hsp.1, hsp.2.2.1⟩
          have hL0_i : L0 = 2 * (D.k i - 3) := by
            dsimp [L0, L0_l]; rw [dif_pos ⟨i, hi⟩]
            have hch : Classical.choose (⟨i, hi⟩ : ∃ j, a = ι (BinaryIRSProfile.domain j)) = i :=
              BinaryIRSProfile.domain.injective (ι.injective ((Classical.choose_spec (⟨i, hi⟩ : ∃ j, a = ι (BinaryIRSProfile.domain j))).symm.trans hi))
            rw [hch, if_pos hk3]
          rw [show pt = .k3U from hpt]; dsimp only [Step15Pt.k1Min]; split_ifs with hd1'
          · have hD1 : K.isD1 i := by by_contra h; have := (hrm_dom_D1 i hi).mpr h; omega
            have hKL := K.pow_dvd_K_M10sh_d2 i hD1; rw [if_neg (by omega)] at hKL
            have hrm1 := (le_rootMultiplicity_iff (mul_ne_zero K.hK1_ne K.hLam1_ne)).mpr hKL
            rw [rootMultiplicity_mul (mul_ne_zero K.hK1_ne K.hLam1_ne)] at hrm1
            have hrm2 := (le_rootMultiplicity_iff K.hK1_ne).mpr (K.pow_dvd_K1_all i)
            rw [hi, ← map_pow, rootMultiplicity_map_eq, hrm_dom_Lam1 i hi, hL0_i]
            have h3' := hk3.1; generalize D.k i = ki at h3' hrm1 hrm2 ⊢
            generalize K.K1.rootMultiplicity (BinaryIRSProfile.domain i ^ 2) = r1 at hrm1 hrm2 ⊢
            generalize K.Lam1.rootMultiplicity (BinaryIRSProfile.domain i ^ 2) = r2 at hrm1 ⊢; omega
          · exact Nat.zero_le _
        · obtain ⟨i, hi⟩ := hdom_of_pt (by simp [pt, hpt])
          have hsp := (K.ptOf_dom_spec i).2.2.2.2.2.2.1 (hi ▸ hpt)
          have hk3 : 3 ≤ D.k i ∧ S.isU0 i := ⟨hsp.1, hsp.2.2.1⟩
          have hL0_i : L0 = 2 * (D.k i - 3) := by
            dsimp [L0, L0_l]; rw [dif_pos ⟨i, hi⟩]
            have hch : Classical.choose (⟨i, hi⟩ : ∃ j, a = ι (BinaryIRSProfile.domain j)) = i :=
              BinaryIRSProfile.domain.injective (ι.injective ((Classical.choose_spec (⟨i, hi⟩ : ∃ j, a = ι (BinaryIRSProfile.domain j))).symm.trans hi))
            rw [hch, if_pos hk3]
          rw [show pt = .k3U_mL from hpt]; dsimp only [Step15Pt.k1Min]; split_ifs with hd1'
          · have hD1 : K.isD1 i := by by_contra h; have := (hrm_dom_D1 i hi).mpr h; omega
            have hKL := K.pow_dvd_K_M10sh_d2 i hD1; rw [if_neg (by omega)] at hKL
            have hrm1 := (le_rootMultiplicity_iff (mul_ne_zero K.hK1_ne K.hLam1_ne)).mpr hKL
            rw [rootMultiplicity_mul (mul_ne_zero K.hK1_ne K.hLam1_ne)] at hrm1
            have hrm2 := (le_rootMultiplicity_iff K.hK1_ne).mpr (K.pow_dvd_K1_all i)
            rw [hi, ← map_pow, rootMultiplicity_map_eq, hrm_dom_Lam1 i hi, hL0_i]
            have h3' := hk3.1; generalize D.k i = ki at h3' hrm1 hrm2 ⊢
            generalize K.K1.rootMultiplicity (BinaryIRSProfile.domain i ^ 2) = r1 at hrm1 hrm2 ⊢
            generalize K.Lam1.rootMultiplicity (BinaryIRSProfile.domain i ^ 2) = r2 at hrm1 ⊢; omega
          · exact Nat.zero_le _
        · rw [show pt = .k3U_mb from hpt, show Step15Pt.k1Min .k3U_mb d2 lam L0 LnoU = 0 from rfl]; exact Nat.zero_le _
      have hdSg : (X - C a) ^ (pt.nu - pt.mVal) ∣ K.Sg2.map ι := by
        rw [← K.Sg2_rm_eq a]; exact pow_rootMultiplicity_dvd _ a
      have hdgr : (X - C a) ^ e1 ∣ K.g2rem.map ι := pow_rootMultiplicity_dvd _ a
      rw [show 4 * a1 + 2 * d2 + 2 * pt.k1Min d2 lam L0 LnoU + (pt.nu - pt.mVal) + e1 =
          (4 * a1 + 2 * d2) + (2 * pt.k1Min d2 lam L0 LnoU + ((pt.nu - pt.mVal) + e1)) by omega,
        pow_add, pow_add, pow_add, pow_add]
      exact mul_dvd_mul (mul_dvd_mul hdp hdU) (mul_dvd_mul hdK1 (mul_dvd_mul hdSg hdgr))
    have hs3 : 3 * pt.mVal ≤ pt.t3 d2 mu e1 := by
      dsimp only [pt, d2, mu, e1]
      generalize K.ptOf a = p; generalize K.d2_l a = d; generalize K.muEx_l a = m; generalize K.e1_l a = e
      cases p <;> simp only [Step15Pt.t3, Step15Pt.isML, Step15Pt.nu, Step15Pt.mVal,
        Step15Pt.m0, Step15Pt.mbad, Step15Pt.m1, Step15Pt.m2, Bool.false_eq_true, false_and, true_and, ↓reduceIte] <;>
        (try split_ifs) <;> omega
    exact tri_of_four_term_id a hT3_ne hT4_ne hidE (s := 3 * pt.mVal)
      (by simpa [show 8 * a1 + 4 * d2 + 3 * pt.mVal + pt.vc0 d2 e1 c L0 LnoU - 3 * pt.mVal =
          8 * a1 + 4 * d2 + pt.vc0 d2 e1 c L0 LnoU by omega] using hd_T1)
      (by simpa [show 4 * a1 + 2 * d2 + 2 * pt.k1Min d2 lam L0 LnoU + (pt.nu - pt.mVal) + 3 * pt.mVal + e1 - 3 * pt.mVal =
          4 * a1 + 2 * d2 + 2 * pt.k1Min d2 lam L0 LnoU + (pt.nu - pt.mVal) + e1 by omega] using hd_T2)
      (by omega) (by omega) hs3 (by omega) hT3_rm (by simpa using hT4_rm)

-- Universal finite-sum bridge for ALL 15-column `Step15Pt` sums over a large enough `S_fin`!

end KerD45KData
end B6402Table4K
end ProximityPrize.SubmissionBinaryLower
